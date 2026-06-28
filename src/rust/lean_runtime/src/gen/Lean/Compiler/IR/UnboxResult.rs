// Lean compiler output
// Module: Lean.Compiler.IR.UnboxResult
// Imports: Lean.Compiler.IR.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_replaceRef};
use crate::r#gen::Lean::Attributes::{l_Lean_TagAttribute_hasTag, l_Lean_registerTagAttribute};
use crate::r#gen::Lean::Compiler::IR::Basic::{
    initialize_Lean_Compiler_IR_Basic, runtime_initialize_Lean_Compiler_IR_Basic,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Prelude::{lean_array_get, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 117, 110, 98, 111, 120, 93, 96, 32, 116, 111, 32, 96, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [96, 58, 32, 82, 101, 99, 117, 114, 115, 105, 118, 101, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 115, 32, 97, 114, 101, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<50> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 50, m_capacity: 50, m_length: 49, m_data: [96, 58, 32, 96, 91, 117, 110, 98, 111, 120, 93, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 97, 100, 100, 101, 100, 32, 116, 111, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [117, 110, 98, 111, 120, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject,11495086036176533314 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 32, 116, 114, 105, 101, 115, 32, 116, 111, 32, 117, 110, 98, 111, 120, 32, 114, 101, 115, 117, 108, 116, 32, 118, 97, 108, 117, 101, 115, 32, 105, 102, 32, 116, 104, 101, 105, 114, 32, 116, 121, 112, 101, 115, 32, 97, 114, 101, 32, 116, 97, 103, 103, 101, 100, 32, 119, 105, 116, 104, 32, 96, 91, 117, 110, 98, 111, 120, 93, 96, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [73, 82, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__6_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [85, 110, 98, 111, 120, 82, 101, 115, 117, 108, 116, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__6_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__6_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__7_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [117, 110, 98, 111, 120, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__7_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__7_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject,896088716302605537 as *mut LeanObject] };
static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__6_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject,8497679236088714616 as *mut LeanObject] };
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__7_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject,11511449672199989246 as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1___closed__0_value: LeanStringObject<116> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 116, m_capacity: 116, m_length: 115, m_data: [84, 97, 103, 115, 32, 116, 121, 112, 101, 115, 32, 116, 104, 97, 116, 32, 116, 104, 101, 32, 99, 111, 109, 112, 105, 108, 101, 114, 32, 115, 104, 111, 117, 108, 100, 32, 117, 110, 98, 111, 120, 32, 105, 102, 32, 116, 104, 101, 121, 32, 111, 99, 99, 117, 114, 32, 105, 110, 32, 114, 101, 115, 117, 108, 116, 32, 118, 97, 108, 117, 101, 115, 46, 10, 10, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 117, 114, 114, 101, 110, 116, 108, 121, 32, 104, 97, 115, 32, 110, 111, 32, 101, 102, 102, 101, 99, 116, 46, 10, 0]};
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 15 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 28 as usize) << 1) | 1) as *mut LeanObject,((( 131 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__1_value) as *mut LeanObject,((( 131 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 21 as usize) << 1) | 1) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__3_value) as *mut LeanObject,((( 19 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__4_value) as *mut LeanObject,((( 28 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    v___x_473_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_473_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_474_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__0);
    v___x_475_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_475_, 0, v___x_474_);
    return v___x_475_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_476_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1);
    v___x_477_ = lean_unsigned_to_nat(0);
    v___x_478_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_478_, 0, v___x_477_);
    lean_ctor_set(v___x_478_, 1, v___x_477_);
    lean_ctor_set(v___x_478_, 2, v___x_477_);
    lean_ctor_set(v___x_478_, 3, v___x_477_);
    lean_ctor_set(v___x_478_, 4, v___x_476_);
    lean_ctor_set(v___x_478_, 5, v___x_476_);
    lean_ctor_set(v___x_478_, 6, v___x_476_);
    lean_ctor_set(v___x_478_, 7, v___x_476_);
    lean_ctor_set(v___x_478_, 8, v___x_476_);
    lean_ctor_set(v___x_478_, 9, v___x_476_);
    return v___x_478_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    v___x_479_ = lean_unsigned_to_nat(32);
    v___x_480_ = lean_mk_empty_array_with_capacity(v___x_479_);
    v___x_481_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_481_, 0, v___x_480_);
    return v___x_481_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_482_: usize = 0;
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_482_ = 5usize;
    v___x_483_ = lean_unsigned_to_nat(0);
    v___x_484_ = lean_unsigned_to_nat(32);
    v___x_485_ = lean_mk_empty_array_with_capacity(v___x_484_);
    v___x_486_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__3);
    v___x_487_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_487_, 0, v___x_486_);
    lean_ctor_set(v___x_487_, 1, v___x_485_);
    lean_ctor_set(v___x_487_, 2, v___x_483_);
    lean_ctor_set(v___x_487_, 3, v___x_483_);
    lean_ctor_set_usize(v___x_487_, 4, v___x_482_);
    return v___x_487_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    v___x_488_ = lean_box(1);
    v___x_489_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__4);
    v___x_490_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__1);
    v___x_491_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_491_, 0, v___x_490_);
    lean_ctor_set(v___x_491_, 1, v___x_489_);
    lean_ctor_set(v___x_491_, 2, v___x_488_);
    return v___x_491_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2(
    mut v_msgData_492_: *mut LeanObject,
    mut v___y_493_: *mut LeanObject,
    mut v___y_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    v___x_496_ = lean_st_ref_get(v___y_494_);
    v_env_497_ = lean_ctor_get(v___x_496_, 0);
    lean_inc_ref(v_env_497_);
    lean_dec(v___x_496_);
    v_options_498_ = lean_ctor_get(v___y_493_, 2);
    v___x_499_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2);
    v___x_500_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5);
    lean_inc_ref(v_options_498_);
    v___x_501_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_501_, 0, v_env_497_);
    lean_ctor_set(v___x_501_, 1, v___x_499_);
    lean_ctor_set(v___x_501_, 2, v___x_500_);
    lean_ctor_set(v___x_501_, 3, v_options_498_);
    v___x_502_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_502_, 0, v___x_501_);
    lean_ctor_set(v___x_502_, 1, v_msgData_492_);
    v___x_503_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_503_, 0, v___x_502_);
    return v___x_503_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_msgData_504_: *mut LeanObject,
    mut v___y_505_: *mut LeanObject,
    mut v___y_506_: *mut LeanObject,
    mut v___y_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_508_: *mut LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2(v_msgData_504_, v___y_505_, v___y_506_);
    lean_dec(v___y_506_);
    lean_dec_ref(v___y_505_);
    return v_res_508_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg(
    mut v_msg_509_: *mut LeanObject,
    mut v___y_510_: *mut LeanObject,
    mut v___y_511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_518_: u8 = 0;
    let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_513_ = lean_ctor_get(v___y_510_, 5);
                v___x_514_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2(v_msg_509_, v___y_510_, v___y_511_);
                v_a_515_ = lean_ctor_get(v___x_514_, 0);
                v_isSharedCheck_523_ = (!lean_is_exclusive(v___x_514_)) as u8;
                if v_isSharedCheck_523_ == 0 {
                    v___x_517_ = v___x_514_;
                    v_isShared_518_ = v_isSharedCheck_523_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_515_);
                    lean_dec(v___x_514_);
                    v___x_517_ = lean_box(0);
                    v_isShared_518_ = v_isSharedCheck_523_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_513_);
                v___x_519_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_519_, 0, v_ref_513_);
                lean_ctor_set(v___x_519_, 1, v_a_515_);
                if v_isShared_518_ == 0 {
                    lean_ctor_set_tag(v___x_517_, 1);
                    lean_ctor_set(v___x_517_, 0, v___x_519_);
                    v___x_521_ = v___x_517_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
                    v___x_521_ = v_reuseFailAlloc_522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_msg_524_: *mut LeanObject,
    mut v___y_525_: *mut LeanObject,
    mut v___y_526_: *mut LeanObject,
    mut v___y_527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_528_: *mut LeanObject = core::ptr::null_mut();
    v_res_528_ = l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg(v_msg_524_, v___y_525_, v___y_526_);
    lean_dec(v___y_526_);
    lean_dec_ref(v___y_525_);
    return v_res_528_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_529_: *mut LeanObject,
    mut v_msg_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_546_: u8 = 0;
    let mut v_cancelTk_x3f_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_548_: u8 = 0;
    let mut v_inheritedTraceOptions_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_534_ = lean_ctor_get(v___y_531_, 0);
    v_fileMap_535_ = lean_ctor_get(v___y_531_, 1);
    v_options_536_ = lean_ctor_get(v___y_531_, 2);
    v_currRecDepth_537_ = lean_ctor_get(v___y_531_, 3);
    v_maxRecDepth_538_ = lean_ctor_get(v___y_531_, 4);
    v_ref_539_ = lean_ctor_get(v___y_531_, 5);
    v_currNamespace_540_ = lean_ctor_get(v___y_531_, 6);
    v_openDecls_541_ = lean_ctor_get(v___y_531_, 7);
    v_initHeartbeats_542_ = lean_ctor_get(v___y_531_, 8);
    v_maxHeartbeats_543_ = lean_ctor_get(v___y_531_, 9);
    v_quotContext_544_ = lean_ctor_get(v___y_531_, 10);
    v_currMacroScope_545_ = lean_ctor_get(v___y_531_, 11);
    v_diag_546_ = lean_ctor_get_uint8(
        v___y_531_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_547_ = lean_ctor_get(v___y_531_, 12);
    v_suppressElabErrors_548_ = lean_ctor_get_uint8(
        v___y_531_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_549_ = lean_ctor_get(v___y_531_, 13);
    v_ref_550_ = l_Lean_replaceRef(v_ref_529_, v_ref_539_);
    lean_inc_ref(v_inheritedTraceOptions_549_);
    lean_inc(v_cancelTk_x3f_547_);
    lean_inc(v_currMacroScope_545_);
    lean_inc(v_quotContext_544_);
    lean_inc(v_maxHeartbeats_543_);
    lean_inc(v_initHeartbeats_542_);
    lean_inc(v_openDecls_541_);
    lean_inc(v_currNamespace_540_);
    lean_inc(v_maxRecDepth_538_);
    lean_inc(v_currRecDepth_537_);
    lean_inc_ref(v_options_536_);
    lean_inc_ref(v_fileMap_535_);
    lean_inc_ref(v_fileName_534_);
    v___x_551_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_551_, 0, v_fileName_534_);
    lean_ctor_set(v___x_551_, 1, v_fileMap_535_);
    lean_ctor_set(v___x_551_, 2, v_options_536_);
    lean_ctor_set(v___x_551_, 3, v_currRecDepth_537_);
    lean_ctor_set(v___x_551_, 4, v_maxRecDepth_538_);
    lean_ctor_set(v___x_551_, 5, v_ref_550_);
    lean_ctor_set(v___x_551_, 6, v_currNamespace_540_);
    lean_ctor_set(v___x_551_, 7, v_openDecls_541_);
    lean_ctor_set(v___x_551_, 8, v_initHeartbeats_542_);
    lean_ctor_set(v___x_551_, 9, v_maxHeartbeats_543_);
    lean_ctor_set(v___x_551_, 10, v_quotContext_544_);
    lean_ctor_set(v___x_551_, 11, v_currMacroScope_545_);
    lean_ctor_set(v___x_551_, 12, v_cancelTk_x3f_547_);
    lean_ctor_set(v___x_551_, 13, v_inheritedTraceOptions_549_);
    lean_ctor_set_uint8(
        v___x_551_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_546_,
    );
    lean_ctor_set_uint8(
        v___x_551_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_548_,
    );
    v___x_552_ = l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg(v_msg_530_, v___x_551_, v___y_532_);
    lean_dec_ref_known(v___x_551_, 14);
    return v___x_552_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_553_: *mut LeanObject,
    mut v_msg_554_: *mut LeanObject,
    mut v___y_555_: *mut LeanObject,
    mut v___y_556_: *mut LeanObject,
    mut v___y_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_558_: *mut LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_553_, v_msg_554_, v___y_555_, v___y_556_);
    lean_dec(v___y_556_);
    lean_dec_ref(v___y_555_);
    lean_dec(v_ref_553_);
    return v_res_558_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    v___x_560_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_561_ = l_Lean_stringToMessageData(v___x_560_);
    return v___x_561_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_563_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_564_ = l_Lean_stringToMessageData(v___x_563_);
    return v___x_564_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_567_ = l_Lean_stringToMessageData(v___x_566_);
    return v___x_567_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_570_ = l_Lean_stringToMessageData(v___x_569_);
    return v___x_570_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_572_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_573_ = l_Lean_stringToMessageData(v___x_572_);
    return v___x_573_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_575_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_576_ = l_Lean_stringToMessageData(v___x_575_);
    return v___x_576_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_578_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_579_ = l_Lean_stringToMessageData(v___x_578_);
    return v___x_579_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_580_: *mut LeanObject,
    mut v_declHint_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v_isExporting_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_609_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: u8 = 0;
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_641_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_584_ = lean_st_ref_get(v___y_582_);
                v_env_585_ = lean_ctor_get(v___x_584_, 0);
                lean_inc_ref(v_env_585_);
                lean_dec(v___x_584_);
                v___x_586_ = l_Lean_Name_isAnonymous(v_declHint_581_);
                if v___x_586_ == 0 {
                    v_isExporting_587_ = lean_ctor_get_uint8(
                        v_env_585_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_587_ == 0 {
                        lean_dec_ref(v_env_585_);
                        lean_dec(v_declHint_581_);
                        v___x_588_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_588_, 0, v_msg_580_);
                        return v___x_588_;
                    } else {
                        lean_inc_ref(v_env_585_);
                        v___x_589_ = l_Lean_Environment_setExporting(v_env_585_, v___x_586_);
                        lean_inc(v_declHint_581_);
                        lean_inc_ref(v___x_589_);
                        v___x_590_ = l_Lean_Environment_contains(
                            v___x_589_,
                            v_declHint_581_,
                            v_isExporting_587_,
                        );
                        if v___x_590_ == 0 {
                            lean_dec_ref(v___x_589_);
                            lean_dec_ref(v_env_585_);
                            lean_dec(v_declHint_581_);
                            v___x_591_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_591_, 0, v_msg_580_);
                            return v___x_591_;
                        } else {
                            v___x_592_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__2);
                            v___x_593_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1_spec__2___closed__5);
                            v___x_594_ = l_Lean_Options_empty;
                            v___x_595_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_595_, 0, v___x_589_);
                            lean_ctor_set(v___x_595_, 1, v___x_592_);
                            lean_ctor_set(v___x_595_, 2, v___x_593_);
                            lean_ctor_set(v___x_595_, 3, v___x_594_);
                            lean_inc(v_declHint_581_);
                            v___x_596_ =
                                l_Lean_MessageData_ofConstName(v_declHint_581_, v___x_586_);
                            v_c_597_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_597_, 0, v___x_595_);
                            lean_ctor_set(v_c_597_, 1, v___x_596_);
                            v___x_598_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_585_, v_declHint_581_);
                            if lean_obj_tag(v___x_598_) == 0 {
                                lean_dec_ref(v_env_585_);
                                lean_dec(v_declHint_581_);
                                v___x_599_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_600_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_600_, 0, v___x_599_);
                                lean_ctor_set(v___x_600_, 1, v_c_597_);
                                v___x_601_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_602_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_602_, 0, v___x_600_);
                                lean_ctor_set(v___x_602_, 1, v___x_601_);
                                v___x_603_ = l_Lean_MessageData_note(v___x_602_);
                                v___x_604_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_604_, 0, v_msg_580_);
                                lean_ctor_set(v___x_604_, 1, v___x_603_);
                                v___x_605_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_605_, 0, v___x_604_);
                                return v___x_605_;
                            } else {
                                v_val_606_ = lean_ctor_get(v___x_598_, 0);
                                v_isSharedCheck_641_ = (!lean_is_exclusive(v___x_598_)) as u8;
                                if v_isSharedCheck_641_ == 0 {
                                    v___x_608_ = v___x_598_;
                                    v_isShared_609_ = v_isSharedCheck_641_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_606_);
                                    lean_dec(v___x_598_);
                                    v___x_608_ = lean_box(0);
                                    v_isShared_609_ = v_isSharedCheck_641_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_585_);
                    lean_dec(v_declHint_581_);
                    v___x_642_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_642_, 0, v_msg_580_);
                    return v___x_642_;
                }
            }
            1 => {
                v___x_610_ = lean_box(0);
                v___x_611_ = l_Lean_Environment_header(v_env_585_);
                lean_dec_ref(v_env_585_);
                v___x_612_ = l_Lean_EnvironmentHeader_moduleNames(v___x_611_);
                v_mod_613_ = lean_array_get(v___x_610_, v___x_612_, v_val_606_);
                lean_dec(v_val_606_);
                lean_dec_ref(v___x_612_);
                v___x_614_ = l_Lean_isPrivateName(v_declHint_581_);
                lean_dec(v_declHint_581_);
                if v___x_614_ == 0 {
                    v___x_615_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_616_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_616_, 0, v___x_615_);
                    lean_ctor_set(v___x_616_, 1, v_c_597_);
                    v___x_617_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_618_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_618_, 0, v___x_616_);
                    lean_ctor_set(v___x_618_, 1, v___x_617_);
                    v___x_619_ = l_Lean_MessageData_ofName(v_mod_613_);
                    v___x_620_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_620_, 0, v___x_618_);
                    lean_ctor_set(v___x_620_, 1, v___x_619_);
                    v___x_621_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_622_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_622_, 0, v___x_620_);
                    lean_ctor_set(v___x_622_, 1, v___x_621_);
                    v___x_623_ = l_Lean_MessageData_note(v___x_622_);
                    v___x_624_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_624_, 0, v_msg_580_);
                    lean_ctor_set(v___x_624_, 1, v___x_623_);
                    if v_isShared_609_ == 0 {
                        lean_ctor_set_tag(v___x_608_, 0);
                        lean_ctor_set(v___x_608_, 0, v___x_624_);
                        v___x_626_ = v___x_608_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
                        v___x_626_ = v_reuseFailAlloc_627_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_628_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_629_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_629_, 0, v___x_628_);
                    lean_ctor_set(v___x_629_, 1, v_c_597_);
                    v___x_630_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_631_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_631_, 0, v___x_629_);
                    lean_ctor_set(v___x_631_, 1, v___x_630_);
                    v___x_632_ = l_Lean_MessageData_ofName(v_mod_613_);
                    v___x_633_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_633_, 0, v___x_631_);
                    lean_ctor_set(v___x_633_, 1, v___x_632_);
                    v___x_634_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_635_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_635_, 0, v___x_633_);
                    lean_ctor_set(v___x_635_, 1, v___x_634_);
                    v___x_636_ = l_Lean_MessageData_note(v___x_635_);
                    v___x_637_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_637_, 0, v_msg_580_);
                    lean_ctor_set(v___x_637_, 1, v___x_636_);
                    if v_isShared_609_ == 0 {
                        lean_ctor_set_tag(v___x_608_, 0);
                        lean_ctor_set(v___x_608_, 0, v___x_637_);
                        v___x_639_ = v___x_608_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
                        v___x_639_ = v_reuseFailAlloc_640_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_626_;
            }
            3 => {
                return v___x_639_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_643_: *mut LeanObject,
    mut v_declHint_644_: *mut LeanObject,
    mut v___y_645_: *mut LeanObject,
    mut v___y_646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_647_: *mut LeanObject = core::ptr::null_mut();
    v_res_647_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_643_, v_declHint_644_, v___y_645_);
    lean_dec(v___y_645_);
    return v_res_647_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_648_: *mut LeanObject,
    mut v_declHint_649_: *mut LeanObject,
    mut v___y_650_: *mut LeanObject,
    mut v___y_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_657_: u8 = 0;
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_653_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_648_, v_declHint_649_, v___y_651_);
                v_a_654_ = lean_ctor_get(v___x_653_, 0);
                v_isSharedCheck_663_ = (!lean_is_exclusive(v___x_653_)) as u8;
                if v_isSharedCheck_663_ == 0 {
                    v___x_656_ = v___x_653_;
                    v_isShared_657_ = v_isSharedCheck_663_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_654_);
                    lean_dec(v___x_653_);
                    v___x_656_ = lean_box(0);
                    v_isShared_657_ = v_isSharedCheck_663_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_658_ = l_Lean_unknownIdentifierMessageTag;
                v___x_659_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_659_, 0, v___x_658_);
                lean_ctor_set(v___x_659_, 1, v_a_654_);
                if v_isShared_657_ == 0 {
                    lean_ctor_set(v___x_656_, 0, v___x_659_);
                    v___x_661_ = v___x_656_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
                    v___x_661_ = v_reuseFailAlloc_662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_661_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_664_: *mut LeanObject,
    mut v_declHint_665_: *mut LeanObject,
    mut v___y_666_: *mut LeanObject,
    mut v___y_667_: *mut LeanObject,
    mut v___y_668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_669_: *mut LeanObject = core::ptr::null_mut();
    v_res_669_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_664_, v_declHint_665_, v___y_666_, v___y_667_);
    lean_dec(v___y_667_);
    lean_dec_ref(v___y_666_);
    return v_res_669_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_670_: *mut LeanObject,
    mut v_msg_671_: *mut LeanObject,
    mut v_declHint_672_: *mut LeanObject,
    mut v___y_673_: *mut LeanObject,
    mut v___y_674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_671_, v_declHint_672_, v___y_673_, v___y_674_);
    v_a_677_ = lean_ctor_get(v___x_676_, 0);
    lean_inc(v_a_677_);
    lean_dec_ref(v___x_676_);
    v___x_678_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_670_, v_a_677_, v___y_673_, v___y_674_);
    return v___x_678_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_679_: *mut LeanObject,
    mut v_msg_680_: *mut LeanObject,
    mut v_declHint_681_: *mut LeanObject,
    mut v___y_682_: *mut LeanObject,
    mut v___y_683_: *mut LeanObject,
    mut v___y_684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_685_: *mut LeanObject = core::ptr::null_mut();
    v_res_685_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ref_679_, v_msg_680_, v_declHint_681_, v___y_682_, v___y_683_);
    lean_dec(v___y_683_);
    lean_dec_ref(v___y_682_);
    lean_dec(v_ref_679_);
    return v_res_685_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    v___x_687_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_688_ = l_Lean_stringToMessageData(v___x_687_);
    return v___x_688_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    v___x_690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_691_ = l_Lean_stringToMessageData(v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_ref_692_: *mut LeanObject,
    mut v_constName_693_: *mut LeanObject,
    mut v___y_694_: *mut LeanObject,
    mut v___y_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: u8 = 0;
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    v___x_697_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_698_ = 0;
    lean_inc(v_constName_693_);
    v___x_699_ = l_Lean_MessageData_ofConstName(v_constName_693_, v___x_698_);
    v___x_700_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_700_, 0, v___x_697_);
    lean_ctor_set(v___x_700_, 1, v___x_699_);
    v___x_701_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_702_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_702_, 0, v___x_700_);
    lean_ctor_set(v___x_702_, 1, v___x_701_);
    v___x_703_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ref_692_, v___x_702_, v_constName_693_, v___y_694_, v___y_695_);
    return v___x_703_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_704_: *mut LeanObject,
    mut v_constName_705_: *mut LeanObject,
    mut v___y_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
    mut v___y_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_709_: *mut LeanObject = core::ptr::null_mut();
    v_res_709_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_704_, v_constName_705_, v___y_706_, v___y_707_);
    lean_dec(v___y_707_);
    lean_dec_ref(v___y_706_);
    lean_dec(v_ref_704_);
    return v_res_709_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_constName_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
    mut v___y_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    v_ref_714_ = lean_ctor_get(v___y_711_, 5);
    v___x_715_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_714_, v_constName_710_, v___y_711_, v___y_712_);
    return v___x_715_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_constName_716_: *mut LeanObject,
    mut v___y_717_: *mut LeanObject,
    mut v___y_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_720_: *mut LeanObject = core::ptr::null_mut();
    v_res_720_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_716_, v___y_717_, v___y_718_);
    lean_dec(v___y_718_);
    lean_dec_ref(v___y_717_);
    return v_res_720_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0(
    mut v_constName_721_: *mut LeanObject,
    mut v___y_722_: *mut LeanObject,
    mut v___y_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: u8 = 0;
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_725_ = lean_st_ref_get(v___y_723_);
                v_env_726_ = lean_ctor_get(v___x_725_, 0);
                lean_inc_ref(v_env_726_);
                lean_dec(v___x_725_);
                v___x_727_ = 0;
                lean_inc(v_constName_721_);
                v___x_728_ = l_Lean_Environment_find_x3f(v_env_726_, v_constName_721_, v___x_727_);
                if lean_obj_tag(v___x_728_) == 0 {
                    v___x_729_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_721_, v___y_722_, v___y_723_);
                    return v___x_729_;
                } else {
                    lean_dec(v_constName_721_);
                    v_val_730_ = lean_ctor_get(v___x_728_, 0);
                    v_isSharedCheck_737_ = (!lean_is_exclusive(v___x_728_)) as u8;
                    if v_isSharedCheck_737_ == 0 {
                        v___x_732_ = v___x_728_;
                        v_isShared_733_ = v_isSharedCheck_737_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_730_);
                        lean_dec(v___x_728_);
                        v___x_732_ = lean_box(0);
                        v_isShared_733_ = v_isSharedCheck_737_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_733_ == 0 {
                    lean_ctor_set_tag(v___x_732_, 0);
                    v___x_735_ = v___x_732_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_736_, 0, v_val_730_);
                    v___x_735_ = v_reuseFailAlloc_736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_735_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0___boxed(
    mut v_constName_738_: *mut LeanObject,
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
    mut v___y_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_742_: *mut LeanObject = core::ptr::null_mut();
    v_res_742_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0(v_constName_738_, v___y_739_, v___y_740_);
    lean_dec(v___y_740_);
    lean_dec_ref(v___y_739_);
    return v_res_742_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    v___x_744_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_745_ = l_Lean_stringToMessageData(v___x_744_);
    return v___x_745_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    v___x_747_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_748_ = l_Lean_stringToMessageData(v___x_747_);
    return v___x_748_;
}
pub unsafe fn _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__4_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
    return v___x_751_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_(
    mut v_declName_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
    mut v___y_754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_760_: u8 = 0;
    let mut v_val_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isRec_762_: u8 = 0;
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: u8 = 0;
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_781_: u8 = 0;
    let mut v_a_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_785_: u8 = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_752_);
                v___x_756_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0(v_declName_752_, v___y_753_, v___y_754_);
                if lean_obj_tag(v___x_756_) == 0 {
                    v_a_757_ = lean_ctor_get(v___x_756_, 0);
                    v_isSharedCheck_781_ = (!lean_is_exclusive(v___x_756_)) as u8;
                    if v_isSharedCheck_781_ == 0 {
                        v___x_759_ = v___x_756_;
                        v_isShared_760_ = v_isSharedCheck_781_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_757_);
                        lean_dec(v___x_756_);
                        v___x_759_ = lean_box(0);
                        v_isShared_760_ = v_isSharedCheck_781_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_752_);
                    v_a_782_ = lean_ctor_get(v___x_756_, 0);
                    v_isSharedCheck_789_ = (!lean_is_exclusive(v___x_756_)) as u8;
                    if v_isSharedCheck_789_ == 0 {
                        v___x_784_ = v___x_756_;
                        v_isShared_785_ = v_isSharedCheck_789_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_782_);
                        lean_dec(v___x_756_);
                        v___x_784_ = lean_box(0);
                        v_isShared_785_ = v_isSharedCheck_789_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_757_) == 5 {
                    v_val_761_ = lean_ctor_get(v_a_757_, 0);
                    lean_inc_ref(v_val_761_);
                    lean_dec_ref_known(v_a_757_, 1);
                    v_isRec_762_ = lean_ctor_get_uint8(
                        v_val_761_,
                        (core::mem::size_of::<*mut LeanObject>() * 6) as u32,
                    );
                    lean_dec_ref(v_val_761_);
                    if v_isRec_762_ == 0 {
                        lean_dec(v_declName_752_);
                        v___x_763_ = lean_box(0);
                        if v_isShared_760_ == 0 {
                            lean_ctor_set(v___x_759_, 0, v___x_763_);
                            v___x_765_ = v___x_759_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_766_, 0, v___x_763_);
                            v___x_765_ = v_reuseFailAlloc_766_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_759_);
                        v___x_767_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_);
                        v___x_768_ = 0;
                        v___x_769_ = l_Lean_MessageData_ofConstName(v_declName_752_, v___x_768_);
                        v___x_770_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_770_, 0, v___x_767_);
                        lean_ctor_set(v___x_770_, 1, v___x_769_);
                        v___x_771_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_);
                        v___x_772_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_772_, 0, v___x_770_);
                        lean_ctor_set(v___x_772_, 1, v___x_771_);
                        v___x_773_ = l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg(v___x_772_, v___y_753_, v___y_754_);
                        return v___x_773_;
                    }
                } else {
                    lean_del_object(v___x_759_);
                    lean_dec(v_a_757_);
                    v___x_774_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__1_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_);
                    v___x_775_ = 0;
                    v___x_776_ = l_Lean_MessageData_ofConstName(v_declName_752_, v___x_775_);
                    v___x_777_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_777_, 0, v___x_774_);
                    lean_ctor_set(v___x_777_, 1, v___x_776_);
                    v___x_778_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0___closed__5_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_);
                    v___x_779_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_779_, 0, v___x_777_);
                    lean_ctor_set(v___x_779_, 1, v___x_778_);
                    v___x_780_ = l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg(v___x_779_, v___y_753_, v___y_754_);
                    return v___x_780_;
                }
            }
            2 => {
                return v___x_765_;
            }
            3 => {
                if v_isShared_785_ == 0 {
                    v___x_787_ = v___x_784_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_788_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_788_, 0, v_a_782_);
                    v___x_787_ = v_reuseFailAlloc_788_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2____boxed(
    mut v_declName_790_: *mut LeanObject,
    mut v___y_791_: *mut LeanObject,
    mut v___y_792_: *mut LeanObject,
    mut v___y_793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_794_: *mut LeanObject = core::ptr::null_mut();
    v_res_794_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___lam__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_(v_declName_790_, v___y_791_, v___y_792_);
    lean_dec(v___y_792_);
    lean_dec_ref(v___y_791_);
    return v_res_794_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: u8 = 0;
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    v___f_810_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__0_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_811_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__2_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_812_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__3_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_813_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_814_ = 0;
    v___x_815_ = lean_box(2);
    v___x_816_ = l_Lean_registerTagAttribute(
        v___x_811_, v___x_812_, v___f_810_, v___x_813_, v___x_814_, v___x_815_,
    );
    return v___x_816_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2____boxed(
    mut v_a_817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_818_: *mut LeanObject = core::ptr::null_mut();
    v_res_818_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_();
    return v_res_818_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_819_: *mut LeanObject,
    mut v_msg_820_: *mut LeanObject,
    mut v___y_821_: *mut LeanObject,
    mut v___y_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    v___x_824_ = l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___redArg(v_msg_820_, v___y_821_, v___y_822_);
    return v___x_824_;
}
pub unsafe fn l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_825_: *mut LeanObject,
    mut v_msg_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
    mut v___y_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Lean_throwError___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__1(v_00_u03b1_825_, v_msg_826_, v___y_827_, v___y_828_);
    lean_dec(v___y_828_);
    lean_dec_ref(v___y_827_);
    return v_res_830_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_831_: *mut LeanObject,
    mut v_constName_832_: *mut LeanObject,
    mut v___y_833_: *mut LeanObject,
    mut v___y_834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0___redArg(v_constName_832_, v___y_833_, v___y_834_);
    return v___x_836_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_837_: *mut LeanObject,
    mut v_constName_838_: *mut LeanObject,
    mut v___y_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_842_: *mut LeanObject = core::ptr::null_mut();
    v_res_842_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_837_, v_constName_838_, v___y_839_, v___y_840_);
    lean_dec(v___y_840_);
    lean_dec_ref(v___y_839_);
    return v_res_842_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03b1_843_: *mut LeanObject,
    mut v_ref_844_: *mut LeanObject,
    mut v_constName_845_: *mut LeanObject,
    mut v___y_846_: *mut LeanObject,
    mut v___y_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    v___x_849_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_ref_844_, v_constName_845_, v___y_846_, v___y_847_);
    return v___x_849_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_850_: *mut LeanObject,
    mut v_ref_851_: *mut LeanObject,
    mut v_constName_852_: *mut LeanObject,
    mut v___y_853_: *mut LeanObject,
    mut v___y_854_: *mut LeanObject,
    mut v___y_855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_856_: *mut LeanObject = core::ptr::null_mut();
    v_res_856_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b1_850_, v_ref_851_, v_constName_852_, v___y_853_, v___y_854_);
    lean_dec(v___y_854_);
    lean_dec_ref(v___y_853_);
    lean_dec(v_ref_851_);
    return v_res_856_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_857_: *mut LeanObject,
    mut v_ref_858_: *mut LeanObject,
    mut v_msg_859_: *mut LeanObject,
    mut v_declHint_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    v___x_864_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_ref_858_, v_msg_859_, v_declHint_860_, v___y_861_, v___y_862_);
    return v___x_864_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_865_: *mut LeanObject,
    mut v_ref_866_: *mut LeanObject,
    mut v_msg_867_: *mut LeanObject,
    mut v_declHint_868_: *mut LeanObject,
    mut v___y_869_: *mut LeanObject,
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_872_: *mut LeanObject = core::ptr::null_mut();
    v_res_872_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03b1_865_, v_ref_866_, v_msg_867_, v_declHint_868_, v___y_869_, v___y_870_);
    lean_dec(v___y_870_);
    lean_dec_ref(v___y_869_);
    lean_dec(v_ref_866_);
    return v_res_872_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_873_: *mut LeanObject,
    mut v_declHint_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    v___x_878_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_873_, v_declHint_874_, v___y_876_);
    return v___x_878_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_879_: *mut LeanObject,
    mut v_declHint_880_: *mut LeanObject,
    mut v___y_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
    mut v___y_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_884_: *mut LeanObject = core::ptr::null_mut();
    v_res_884_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_879_, v_declHint_880_, v___y_881_, v___y_882_);
    lean_dec(v___y_882_);
    lean_dec_ref(v___y_881_);
    return v_res_884_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_885_: *mut LeanObject,
    mut v_ref_886_: *mut LeanObject,
    mut v_msg_887_: *mut LeanObject,
    mut v___y_888_: *mut LeanObject,
    mut v___y_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    v___x_891_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_886_, v_msg_887_, v___y_888_, v___y_889_);
    return v___x_891_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_892_: *mut LeanObject,
    mut v_ref_893_: *mut LeanObject,
    mut v_msg_894_: *mut LeanObject,
    mut v___y_895_: *mut LeanObject,
    mut v___y_896_: *mut LeanObject,
    mut v___y_897_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_898_: *mut LeanObject = core::ptr::null_mut();
    v_res_898_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_892_, v_ref_893_, v_msg_894_, v___y_895_, v___y_896_);
    lean_dec(v___y_896_);
    lean_dec_ref(v___y_895_);
    lean_dec(v_ref_893_);
    return v_res_898_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1()
-> *mut LeanObject {
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    v___x_901_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_902_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1___closed__0;
    v___x_903_ = l_Lean_addBuiltinDocString(v___x_901_, v___x_902_);
    return v___x_903_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1___boxed(
    mut v_a_904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_905_: *mut LeanObject = core::ptr::null_mut();
    v_res_905_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1();
    return v_res_905_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3()
-> *mut LeanObject {
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    v___x_932_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn___closed__8_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_;
    v___x_933_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___closed__6;
    v___x_934_ = l_Lean_addBuiltinDeclarationRanges(v___x_932_, v___x_933_);
    return v___x_934_;
}
pub unsafe fn l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3___boxed(
    mut v_a_935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_936_: *mut LeanObject = core::ptr::null_mut();
    v_res_936_ = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3();
    return v_res_936_;
}
pub unsafe fn l_Lean_IR_UnboxResult_hasUnboxAttr(
    mut v_env_937_: *mut LeanObject,
    mut v_n_938_: *mut LeanObject,
) -> u8 {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    v___x_939_ = l_Lean_IR_UnboxResult_unboxAttr;
    v___x_940_ = l_Lean_TagAttribute_hasTag(v___x_939_, v_env_937_, v_n_938_);
    return v___x_940_;
}
pub unsafe fn l_Lean_IR_UnboxResult_hasUnboxAttr___boxed(
    mut v_env_941_: *mut LeanObject,
    mut v_n_942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_943_: u8 = 0;
    let mut v_r_944_: *mut LeanObject = core::ptr::null_mut();
    v_res_943_ = l_Lean_IR_UnboxResult_hasUnboxAttr(v_env_941_, v_n_942_);
    v_r_944_ = lean_box((v_res_943_) as usize);
    return v_r_944_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_IR_UnboxResult(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_initFn_00___x40_Lean_Compiler_IR_UnboxResult_1925234477____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_IR_UnboxResult_unboxAttr = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_IR_UnboxResult_unboxAttr);
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_docString__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_IR_UnboxResult_0__Lean_IR_UnboxResult_unboxAttr___regBuiltin_Lean_IR_UnboxResult_unboxAttr_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_IR_UnboxResult(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_IR_UnboxResult(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_IR_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_IR_UnboxResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_IR_UnboxResult(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_IR_UnboxResult(builtin);
}
