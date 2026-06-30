// Lean compiler output
// Module: Lean.Compiler.LCNF.Util
// Imports: Init.Data.FloatArray.Basic Lean.CoreM Lean.Util.Recognizers
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_uget_borrowed,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_lt,
    lean_st_ref_get, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::FloatArray::Basic::{
    initialize_Init_Data_FloatArray_Basic, runtime_initialize_Init_Data_FloatArray_Basic,
};
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::CoreM::{initialize_Lean_CoreM, runtime_initialize_Lean_CoreM};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_appArg_x21, l_Lean_Expr_isAppOfArity};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Recognizers::{
    initialize_Lean_Util_Recognizers, runtime_initialize_Lean_Util_Recognizers,
};
pub static l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [108, 99, 67, 97, 115, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1_value: leanh::LeanCtorObject<3> =
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
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0_value)
                as *mut leanh::LeanObject,
            9297529361438902301 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0_value:
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
    m_data: [83, 116, 114, 105, 110, 103, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0_value)
            as *mut leanh::LeanObject,
        3136308715950998022 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 73, 110, 116, 56, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2_value)
            as *mut leanh::LeanObject,
        15764114953608429200 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4_value:
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
    m_data: [85, 73, 110, 116, 49, 54, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4_value)
            as *mut leanh::LeanObject,
        9755723410228041222 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6_value:
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
    m_data: [85, 73, 110, 116, 51, 50, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6_value)
            as *mut leanh::LeanObject,
        13474504806189678690 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8_value:
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
    m_data: [85, 73, 110, 116, 54, 52, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8_value)
            as *mut leanh::LeanObject,
        2954612489107370298 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [85, 83, 105, 122, 101, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10_value)
            as *mut leanh::LeanObject,
        17712594561405737325 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 108, 111, 97, 116, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12_value)
            as *mut leanh::LeanObject,
        4889978610488853816 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [70, 108, 111, 97, 116, 51, 50, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14_value)
            as *mut leanh::LeanObject,
        16690552700474419446 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [84, 104, 117, 110, 107, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16_value)
            as *mut leanh::LeanObject,
        15912191227757008981 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18_value:
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
    m_data: [84, 97, 115, 107, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18_value)
            as *mut leanh::LeanObject,
        1347124975762375613 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20_value)
            as *mut leanh::LeanObject,
        8749134177695247953 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22_value:
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
    m_data: [66, 121, 116, 101, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22_value)
            as *mut leanh::LeanObject,
        14803615792343879184 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [70, 108, 111, 97, 116, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24_value)
            as *mut leanh::LeanObject,
        2130556170951526559 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26_value)
            as *mut leanh::LeanObject,
        11442535297760353691 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [73, 110, 116, 0],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28_value)
            as *mut leanh::LeanObject,
        7009148538150066493 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30_value:
    leanh::LeanArrayObject<15> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 15) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 15,
    m_capacity: 15,
    m_data: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_isCompilerRelevantMData(
    mut v___mdata_524_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_525_: u8 = 0;
    v___x_525_ = 0;
    return v___x_525_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isCompilerRelevantMData___boxed(
    mut v___mdata_526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_527_: u8 = 0;
    let mut v_r_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lean_Compiler_LCNF_isCompilerRelevantMData(v___mdata_526_);
    leanh::lean_dec(v___mdata_526_);
    v_r_528_ = leanh::lean_box((v_res_527_) as usize);
    return v_r_528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isLcCast_x3f(
    mut v_e_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_533_ = l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1;
    v___x_534_ = leanh::lean_unsigned_to_nat(3);
    v___x_535_ = l_Lean_Expr_isAppOfArity(v_e_532_, v___x_533_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_536_ = leanh::lean_box(0);
        return v___x_536_;
    } else {
        let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_537_ = l_Lean_Expr_appArg_x21(v_e_532_);
        v___x_538_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_538_, 0, v___x_537_);
        return v___x_538_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isLcCast_x3f___boxed(
    mut v_e_539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Compiler_LCNF_isLcCast_x3f(v_e_539_);
    leanh::lean_dec_ref(v_e_539_);
    return v_res_540_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_541_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0);
    v___x_543_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_543_, 0, v___x_542_);
    return v___x_543_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_545_ = leanh::lean_unsigned_to_nat(0);
    v___x_546_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_546_, 0, v___x_545_);
    leanh::lean_ctor_set(v___x_546_, 1, v___x_545_);
    leanh::lean_ctor_set(v___x_546_, 2, v___x_545_);
    leanh::lean_ctor_set(v___x_546_, 3, v___x_545_);
    leanh::lean_ctor_set(v___x_546_, 4, v___x_544_);
    leanh::lean_ctor_set(v___x_546_, 5, v___x_544_);
    leanh::lean_ctor_set(v___x_546_, 6, v___x_544_);
    leanh::lean_ctor_set(v___x_546_, 7, v___x_544_);
    leanh::lean_ctor_set(v___x_546_, 8, v___x_544_);
    leanh::lean_ctor_set(v___x_546_, 9, v___x_544_);
    return v___x_546_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = leanh::lean_unsigned_to_nat(32);
    v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
    v___x_549_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_549_, 0, v___x_548_);
    return v___x_549_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_550_: usize = 0;
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = 5usize;
    v___x_551_ = leanh::lean_unsigned_to_nat(0);
    v___x_552_ = leanh::lean_unsigned_to_nat(32);
    v___x_553_ = lean_mk_empty_array_with_capacity(v___x_552_);
    v___x_554_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3);
    v___x_555_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_555_, 0, v___x_554_);
    leanh::lean_ctor_set(v___x_555_, 1, v___x_553_);
    leanh::lean_ctor_set(v___x_555_, 2, v___x_551_);
    leanh::lean_ctor_set(v___x_555_, 3, v___x_551_);
    leanh::lean_ctor_set_usize(v___x_555_, 4, v___x_550_);
    return v___x_555_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = leanh::lean_box(1);
    v___x_557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4);
    v___x_558_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_559_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_559_, 0, v___x_558_);
    leanh::lean_ctor_set(v___x_559_, 1, v___x_557_);
    leanh::lean_ctor_set(v___x_559_, 2, v___x_556_);
    return v___x_559_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_560_: *mut leanh::LeanObject,
    mut v___y_561_: *mut leanh::LeanObject,
    mut v___y_562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = lean_st_ref_get(v___y_562_);
    v_env_565_ = leanh::lean_ctor_get(v___x_564_, 0);
    leanh::lean_inc_ref(v_env_565_);
    leanh::lean_dec(v___x_564_);
    v_options_566_ = leanh::lean_ctor_get(v___y_561_, 2);
    v___x_567_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
    v___x_568_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5);
    leanh::lean_inc_ref(v_options_566_);
    v___x_569_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_569_, 0, v_env_565_);
    leanh::lean_ctor_set(v___x_569_, 1, v___x_567_);
    leanh::lean_ctor_set(v___x_569_, 2, v___x_568_);
    leanh::lean_ctor_set(v___x_569_, 3, v_options_566_);
    v___x_570_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_570_, 0, v___x_569_);
    leanh::lean_ctor_set(v___x_570_, 1, v_msgData_560_);
    v___x_571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_571_, 0, v___x_570_);
    return v___x_571_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_572_: *mut leanh::LeanObject,
    mut v___y_573_: *mut leanh::LeanObject,
    mut v___y_574_: *mut leanh::LeanObject,
    mut v___y_575_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_576_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_572_, v___y_573_, v___y_574_);
    leanh::lean_dec(v___y_574_);
    leanh::lean_dec_ref(v___y_573_);
    return v_res_576_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_577_: *mut leanh::LeanObject,
    mut v___y_578_: *mut leanh::LeanObject,
    mut v___y_579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_581_ = leanh::lean_ctor_get(v___y_578_, 5);
                v___x_582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_577_, v___y_578_, v___y_579_);
                v_a_583_ = leanh::lean_ctor_get(v___x_582_, 0);
                v_isSharedCheck_591_ = (!leanh::lean_is_exclusive(v___x_582_)) as u8;
                if v_isSharedCheck_591_ == 0 {
                    v___x_585_ = v___x_582_;
                    v_isShared_586_ = v_isSharedCheck_591_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_583_);
                    leanh::lean_dec(v___x_582_);
                    v___x_585_ = leanh::lean_box(0);
                    v_isShared_586_ = v_isSharedCheck_591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_581_);
                v___x_587_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_587_, 0, v_ref_581_);
                leanh::lean_ctor_set(v___x_587_, 1, v_a_583_);
                if v_isShared_586_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_585_, 1);
                    leanh::lean_ctor_set(v___x_585_, 0, v___x_587_);
                    v___x_589_ = v___x_585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
                    v___x_589_ = v_reuseFailAlloc_590_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_592_: *mut leanh::LeanObject,
    mut v___y_593_: *mut leanh::LeanObject,
    mut v___y_594_: *mut leanh::LeanObject,
    mut v___y_595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_592_, v___y_593_, v___y_594_);
    leanh::lean_dec(v___y_594_);
    leanh::lean_dec_ref(v___y_593_);
    return v_res_596_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_597_: *mut leanh::LeanObject,
    mut v_msg_598_: *mut leanh::LeanObject,
    mut v___y_599_: *mut leanh::LeanObject,
    mut v___y_600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_614_: u8 = 0;
    let mut v_cancelTk_x3f_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_616_: u8 = 0;
    let mut v_inheritedTraceOptions_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_602_ = leanh::lean_ctor_get(v___y_599_, 0);
    v_fileMap_603_ = leanh::lean_ctor_get(v___y_599_, 1);
    v_options_604_ = leanh::lean_ctor_get(v___y_599_, 2);
    v_currRecDepth_605_ = leanh::lean_ctor_get(v___y_599_, 3);
    v_maxRecDepth_606_ = leanh::lean_ctor_get(v___y_599_, 4);
    v_ref_607_ = leanh::lean_ctor_get(v___y_599_, 5);
    v_currNamespace_608_ = leanh::lean_ctor_get(v___y_599_, 6);
    v_openDecls_609_ = leanh::lean_ctor_get(v___y_599_, 7);
    v_initHeartbeats_610_ = leanh::lean_ctor_get(v___y_599_, 8);
    v_maxHeartbeats_611_ = leanh::lean_ctor_get(v___y_599_, 9);
    v_quotContext_612_ = leanh::lean_ctor_get(v___y_599_, 10);
    v_currMacroScope_613_ = leanh::lean_ctor_get(v___y_599_, 11);
    v_diag_614_ = leanh::lean_ctor_get_uint8(
        v___y_599_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_615_ = leanh::lean_ctor_get(v___y_599_, 12);
    v_suppressElabErrors_616_ = leanh::lean_ctor_get_uint8(
        v___y_599_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_617_ = leanh::lean_ctor_get(v___y_599_, 13);
    v_ref_618_ = l_Lean_replaceRef(v_ref_597_, v_ref_607_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_617_);
    leanh::lean_inc(v_cancelTk_x3f_615_);
    leanh::lean_inc(v_currMacroScope_613_);
    leanh::lean_inc(v_quotContext_612_);
    leanh::lean_inc(v_maxHeartbeats_611_);
    leanh::lean_inc(v_initHeartbeats_610_);
    leanh::lean_inc(v_openDecls_609_);
    leanh::lean_inc(v_currNamespace_608_);
    leanh::lean_inc(v_maxRecDepth_606_);
    leanh::lean_inc(v_currRecDepth_605_);
    leanh::lean_inc_ref(v_options_604_);
    leanh::lean_inc_ref(v_fileMap_603_);
    leanh::lean_inc_ref(v_fileName_602_);
    v___x_619_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_619_, 0, v_fileName_602_);
    leanh::lean_ctor_set(v___x_619_, 1, v_fileMap_603_);
    leanh::lean_ctor_set(v___x_619_, 2, v_options_604_);
    leanh::lean_ctor_set(v___x_619_, 3, v_currRecDepth_605_);
    leanh::lean_ctor_set(v___x_619_, 4, v_maxRecDepth_606_);
    leanh::lean_ctor_set(v___x_619_, 5, v_ref_618_);
    leanh::lean_ctor_set(v___x_619_, 6, v_currNamespace_608_);
    leanh::lean_ctor_set(v___x_619_, 7, v_openDecls_609_);
    leanh::lean_ctor_set(v___x_619_, 8, v_initHeartbeats_610_);
    leanh::lean_ctor_set(v___x_619_, 9, v_maxHeartbeats_611_);
    leanh::lean_ctor_set(v___x_619_, 10, v_quotContext_612_);
    leanh::lean_ctor_set(v___x_619_, 11, v_currMacroScope_613_);
    leanh::lean_ctor_set(v___x_619_, 12, v_cancelTk_x3f_615_);
    leanh::lean_ctor_set(v___x_619_, 13, v_inheritedTraceOptions_617_);
    leanh::lean_ctor_set_uint8(
        v___x_619_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_614_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_619_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_616_,
    );
    v___x_620_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_598_, v___x_619_, v___y_600_);
    leanh::lean_dec_ref_known(v___x_619_, 14);
    return v___x_620_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_621_: *mut leanh::LeanObject,
    mut v_msg_622_: *mut leanh::LeanObject,
    mut v___y_623_: *mut leanh::LeanObject,
    mut v___y_624_: *mut leanh::LeanObject,
    mut v___y_625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_621_, v_msg_622_, v___y_623_, v___y_624_);
    leanh::lean_dec(v___y_624_);
    leanh::lean_dec_ref(v___y_623_);
    leanh::lean_dec(v_ref_621_);
    return v_res_626_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
    return v___x_629_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
    return v___x_632_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
    return v___x_638_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
    return v___x_641_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
    return v___x_644_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
    return v___x_647_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_648_: *mut leanh::LeanObject,
    mut v_declHint_649_: *mut leanh::LeanObject,
    mut v___y_650_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v_isExporting_655_: u8 = 0;
    let mut v___x_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_709_: u8 = 0;
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_652_ = lean_st_ref_get(v___y_650_);
                v_env_653_ = leanh::lean_ctor_get(v___x_652_, 0);
                leanh::lean_inc_ref(v_env_653_);
                leanh::lean_dec(v___x_652_);
                v___x_654_ = l_Lean_Name_isAnonymous(v_declHint_649_);
                if v___x_654_ == 0 {
                    v_isExporting_655_ = leanh::lean_ctor_get_uint8(
                        v_env_653_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_655_ == 0 {
                        leanh::lean_dec_ref(v_env_653_);
                        leanh::lean_dec(v_declHint_649_);
                        v___x_656_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_656_, 0, v_msg_648_);
                        return v___x_656_;
                    } else {
                        leanh::lean_inc_ref(v_env_653_);
                        v___x_657_ = l_Lean_Environment_setExporting(v_env_653_, v___x_654_);
                        leanh::lean_inc(v_declHint_649_);
                        leanh::lean_inc_ref(v___x_657_);
                        v___x_658_ = l_Lean_Environment_contains(
                            v___x_657_,
                            v_declHint_649_,
                            v_isExporting_655_,
                        );
                        if v___x_658_ == 0 {
                            leanh::lean_dec_ref(v___x_657_);
                            leanh::lean_dec_ref(v_env_653_);
                            leanh::lean_dec(v_declHint_649_);
                            v___x_659_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_659_, 0, v_msg_648_);
                            return v___x_659_;
                        } else {
                            v___x_660_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_661_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5);
                            v___x_662_ = l_Lean_Options_empty;
                            v___x_663_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_663_, 0, v___x_657_);
                            leanh::lean_ctor_set(v___x_663_, 1, v___x_660_);
                            leanh::lean_ctor_set(v___x_663_, 2, v___x_661_);
                            leanh::lean_ctor_set(v___x_663_, 3, v___x_662_);
                            leanh::lean_inc(v_declHint_649_);
                            v___x_664_ =
                                l_Lean_MessageData_ofConstName(v_declHint_649_, v___x_654_);
                            v_c_665_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_665_, 0, v___x_663_);
                            leanh::lean_ctor_set(v_c_665_, 1, v___x_664_);
                            v___x_666_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_653_, v_declHint_649_);
                            if leanh::lean_obj_tag(v___x_666_) == 0 {
                                leanh::lean_dec_ref(v_env_653_);
                                leanh::lean_dec(v_declHint_649_);
                                v___x_667_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
                                leanh::lean_ctor_set(v___x_668_, 1, v_c_665_);
                                v___x_669_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_670_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_670_, 0, v___x_668_);
                                leanh::lean_ctor_set(v___x_670_, 1, v___x_669_);
                                v___x_671_ = l_Lean_MessageData_note(v___x_670_);
                                v___x_672_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_672_, 0, v_msg_648_);
                                leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
                                v___x_673_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_673_, 0, v___x_672_);
                                return v___x_673_;
                            } else {
                                v_val_674_ = leanh::lean_ctor_get(v___x_666_, 0);
                                v_isSharedCheck_709_ =
                                    (!leanh::lean_is_exclusive(v___x_666_)) as u8;
                                if v_isSharedCheck_709_ == 0 {
                                    v___x_676_ = v___x_666_;
                                    v_isShared_677_ = v_isSharedCheck_709_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_674_);
                                    leanh::lean_dec(v___x_666_);
                                    v___x_676_ = leanh::lean_box(0);
                                    v_isShared_677_ = v_isSharedCheck_709_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_653_);
                    leanh::lean_dec(v_declHint_649_);
                    v___x_710_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_710_, 0, v_msg_648_);
                    return v___x_710_;
                }
            }
            1 => {
                v___x_678_ = leanh::lean_box(0);
                v___x_679_ = l_Lean_Environment_header(v_env_653_);
                leanh::lean_dec_ref(v_env_653_);
                v___x_680_ = l_Lean_EnvironmentHeader_moduleNames(v___x_679_);
                v_mod_681_ = lean_array_get(v___x_678_, v___x_680_, v_val_674_);
                leanh::lean_dec(v_val_674_);
                leanh::lean_dec_ref(v___x_680_);
                v___x_682_ = l_Lean_isPrivateName(v_declHint_649_);
                leanh::lean_dec(v_declHint_649_);
                if v___x_682_ == 0 {
                    v___x_683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_684_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_684_, 0, v___x_683_);
                    leanh::lean_ctor_set(v___x_684_, 1, v_c_665_);
                    v___x_685_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_686_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_686_, 0, v___x_684_);
                    leanh::lean_ctor_set(v___x_686_, 1, v___x_685_);
                    v___x_687_ = l_Lean_MessageData_ofName(v_mod_681_);
                    v___x_688_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_688_, 0, v___x_686_);
                    leanh::lean_ctor_set(v___x_688_, 1, v___x_687_);
                    v___x_689_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_690_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_690_, 0, v___x_688_);
                    leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
                    v___x_691_ = l_Lean_MessageData_note(v___x_690_);
                    v___x_692_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_692_, 0, v_msg_648_);
                    leanh::lean_ctor_set(v___x_692_, 1, v___x_691_);
                    if v_isShared_677_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_676_, 0);
                        leanh::lean_ctor_set(v___x_676_, 0, v___x_692_);
                        v___x_694_ = v___x_676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_695_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
                        v___x_694_ = v_reuseFailAlloc_695_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_697_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_697_, 0, v___x_696_);
                    leanh::lean_ctor_set(v___x_697_, 1, v_c_665_);
                    v___x_698_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_699_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_699_, 0, v___x_697_);
                    leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
                    v___x_700_ = l_Lean_MessageData_ofName(v_mod_681_);
                    v___x_701_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_701_, 0, v___x_699_);
                    leanh::lean_ctor_set(v___x_701_, 1, v___x_700_);
                    v___x_702_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_703_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_703_, 0, v___x_701_);
                    leanh::lean_ctor_set(v___x_703_, 1, v___x_702_);
                    v___x_704_ = l_Lean_MessageData_note(v___x_703_);
                    v___x_705_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_705_, 0, v_msg_648_);
                    leanh::lean_ctor_set(v___x_705_, 1, v___x_704_);
                    if v_isShared_677_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_676_, 0);
                        leanh::lean_ctor_set(v___x_676_, 0, v___x_705_);
                        v___x_707_ = v___x_676_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_708_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
                        v___x_707_ = v_reuseFailAlloc_708_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_694_;
            }
            3 => {
                return v___x_707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_711_: *mut leanh::LeanObject,
    mut v_declHint_712_: *mut leanh::LeanObject,
    mut v___y_713_: *mut leanh::LeanObject,
    mut v___y_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_711_, v_declHint_712_, v___y_713_);
    leanh::lean_dec(v___y_713_);
    return v_res_715_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_716_: *mut leanh::LeanObject,
    mut v_declHint_717_: *mut leanh::LeanObject,
    mut v___y_718_: *mut leanh::LeanObject,
    mut v___y_719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_725_: u8 = 0;
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_716_, v_declHint_717_, v___y_719_);
                v_a_722_ = leanh::lean_ctor_get(v___x_721_, 0);
                v_isSharedCheck_731_ = (!leanh::lean_is_exclusive(v___x_721_)) as u8;
                if v_isSharedCheck_731_ == 0 {
                    v___x_724_ = v___x_721_;
                    v_isShared_725_ = v_isSharedCheck_731_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_722_);
                    leanh::lean_dec(v___x_721_);
                    v___x_724_ = leanh::lean_box(0);
                    v_isShared_725_ = v_isSharedCheck_731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_726_ = l_Lean_unknownIdentifierMessageTag;
                v___x_727_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_727_, 0, v___x_726_);
                leanh::lean_ctor_set(v___x_727_, 1, v_a_722_);
                if v_isShared_725_ == 0 {
                    leanh::lean_ctor_set(v___x_724_, 0, v___x_727_);
                    v___x_729_ = v___x_724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_730_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
                    v___x_729_ = v_reuseFailAlloc_730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_732_: *mut leanh::LeanObject,
    mut v_declHint_733_: *mut leanh::LeanObject,
    mut v___y_734_: *mut leanh::LeanObject,
    mut v___y_735_: *mut leanh::LeanObject,
    mut v___y_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_732_, v_declHint_733_, v___y_734_, v___y_735_);
    leanh::lean_dec(v___y_735_);
    leanh::lean_dec_ref(v___y_734_);
    return v_res_737_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_738_: *mut leanh::LeanObject,
    mut v_msg_739_: *mut leanh::LeanObject,
    mut v_declHint_740_: *mut leanh::LeanObject,
    mut v___y_741_: *mut leanh::LeanObject,
    mut v___y_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_739_, v_declHint_740_, v___y_741_, v___y_742_);
    v_a_745_ = leanh::lean_ctor_get(v___x_744_, 0);
    leanh::lean_inc(v_a_745_);
    leanh::lean_dec_ref(v___x_744_);
    v___x_746_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_738_, v_a_745_, v___y_741_, v___y_742_);
    return v___x_746_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_747_: *mut leanh::LeanObject,
    mut v_msg_748_: *mut leanh::LeanObject,
    mut v_declHint_749_: *mut leanh::LeanObject,
    mut v___y_750_: *mut leanh::LeanObject,
    mut v___y_751_: *mut leanh::LeanObject,
    mut v___y_752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_747_, v_msg_748_, v_declHint_749_, v___y_750_, v___y_751_);
    leanh::lean_dec(v___y_751_);
    leanh::lean_dec_ref(v___y_750_);
    leanh::lean_dec(v_ref_747_);
    return v_res_753_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_760_: *mut leanh::LeanObject,
    mut v_constName_761_: *mut leanh::LeanObject,
    mut v___y_762_: *mut leanh::LeanObject,
    mut v___y_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_766_ = 0;
    leanh::lean_inc(v_constName_761_);
    v___x_767_ = l_Lean_MessageData_ofConstName(v_constName_761_, v___x_766_);
    v___x_768_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_768_, 0, v___x_765_);
    leanh::lean_ctor_set(v___x_768_, 1, v___x_767_);
    v___x_769_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_770_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_770_, 0, v___x_768_);
    leanh::lean_ctor_set(v___x_770_, 1, v___x_769_);
    v___x_771_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_760_, v___x_770_, v_constName_761_, v___y_762_, v___y_763_);
    return v___x_771_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_772_: *mut leanh::LeanObject,
    mut v_constName_773_: *mut leanh::LeanObject,
    mut v___y_774_: *mut leanh::LeanObject,
    mut v___y_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(v_ref_772_, v_constName_773_, v___y_774_, v___y_775_);
    leanh::lean_dec(v___y_775_);
    leanh::lean_dec_ref(v___y_774_);
    leanh::lean_dec(v_ref_772_);
    return v_res_777_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(
    mut v_constName_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
    mut v___y_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_782_ = leanh::lean_ctor_get(v___y_779_, 5);
    v___x_783_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(v_ref_782_, v_constName_778_, v___y_779_, v___y_780_);
    return v___x_783_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(v_constName_784_, v___y_785_, v___y_786_);
    leanh::lean_dec(v___y_786_);
    leanh::lean_dec_ref(v___y_785_);
    return v_res_788_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0(
    mut v_constName_789_: *mut leanh::LeanObject,
    mut v___y_790_: *mut leanh::LeanObject,
    mut v___y_791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_793_ = lean_st_ref_get(v___y_791_);
                v_env_794_ = leanh::lean_ctor_get(v___x_793_, 0);
                leanh::lean_inc_ref(v_env_794_);
                leanh::lean_dec(v___x_793_);
                v___x_795_ = 0;
                leanh::lean_inc(v_constName_789_);
                v___x_796_ = l_Lean_Environment_find_x3f(v_env_794_, v_constName_789_, v___x_795_);
                if leanh::lean_obj_tag(v___x_796_) == 0 {
                    v___x_797_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(v_constName_789_, v___y_790_, v___y_791_);
                    return v___x_797_;
                } else {
                    leanh::lean_dec(v_constName_789_);
                    v_val_798_ = leanh::lean_ctor_get(v___x_796_, 0);
                    v_isSharedCheck_805_ = (!leanh::lean_is_exclusive(v___x_796_)) as u8;
                    if v_isSharedCheck_805_ == 0 {
                        v___x_800_ = v___x_796_;
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_798_);
                        leanh::lean_dec(v___x_796_);
                        v___x_800_ = leanh::lean_box(0);
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_801_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_800_, 0);
                    v___x_803_ = v___x_800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_798_);
                    v___x_803_ = v_reuseFailAlloc_804_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0___boxed(
    mut v_constName_806_: *mut leanh::LeanObject,
    mut v___y_807_: *mut leanh::LeanObject,
    mut v___y_808_: *mut leanh::LeanObject,
    mut v___y_809_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0(
        v_constName_806_,
        v___y_807_,
        v___y_808_,
    );
    leanh::lean_dec(v___y_808_);
    leanh::lean_dec_ref(v___y_807_);
    return v_res_810_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getCtorArity_x3f(
    mut v_declName_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v_val_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v_numParams_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_838_: u8 = 0;
    let mut v_a_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_842_: u8 = 0;
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_815_ =
                    l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0(
                        v_declName_811_,
                        v_a_812_,
                        v_a_813_,
                    );
                if leanh::lean_obj_tag(v___x_815_) == 0 {
                    v_a_816_ = leanh::lean_ctor_get(v___x_815_, 0);
                    v_isSharedCheck_838_ = (!leanh::lean_is_exclusive(v___x_815_)) as u8;
                    if v_isSharedCheck_838_ == 0 {
                        v___x_818_ = v___x_815_;
                        v_isShared_819_ = v_isSharedCheck_838_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_816_);
                        leanh::lean_dec(v___x_815_);
                        v___x_818_ = leanh::lean_box(0);
                        v_isShared_819_ = v_isSharedCheck_838_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_839_ = leanh::lean_ctor_get(v___x_815_, 0);
                    v_isSharedCheck_846_ = (!leanh::lean_is_exclusive(v___x_815_)) as u8;
                    if v_isSharedCheck_846_ == 0 {
                        v___x_841_ = v___x_815_;
                        v_isShared_842_ = v_isSharedCheck_846_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_839_);
                        leanh::lean_dec(v___x_815_);
                        v___x_841_ = leanh::lean_box(0);
                        v_isShared_842_ = v_isSharedCheck_846_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_816_) == 6 {
                    v_val_820_ = leanh::lean_ctor_get(v_a_816_, 0);
                    v_isSharedCheck_833_ = (!leanh::lean_is_exclusive(v_a_816_)) as u8;
                    if v_isSharedCheck_833_ == 0 {
                        v___x_822_ = v_a_816_;
                        v_isShared_823_ = v_isSharedCheck_833_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_820_);
                        leanh::lean_dec(v_a_816_);
                        v___x_822_ = leanh::lean_box(0);
                        v_isShared_823_ = v_isSharedCheck_833_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_816_);
                    v___x_834_ = leanh::lean_box(0);
                    if v_isShared_819_ == 0 {
                        leanh::lean_ctor_set(v___x_818_, 0, v___x_834_);
                        v___x_836_ = v___x_818_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
                        v___x_836_ = v_reuseFailAlloc_837_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_numParams_824_ = leanh::lean_ctor_get(v_val_820_, 3);
                leanh::lean_inc(v_numParams_824_);
                v_numFields_825_ = leanh::lean_ctor_get(v_val_820_, 4);
                leanh::lean_inc(v_numFields_825_);
                leanh::lean_dec_ref(v_val_820_);
                v___x_826_ = lean_nat_add(v_numParams_824_, v_numFields_825_);
                leanh::lean_dec(v_numFields_825_);
                leanh::lean_dec(v_numParams_824_);
                if v_isShared_823_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_822_, 1);
                    leanh::lean_ctor_set(v___x_822_, 0, v___x_826_);
                    v___x_828_ = v___x_822_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_826_);
                    v___x_828_ = v_reuseFailAlloc_832_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_819_ == 0 {
                    leanh::lean_ctor_set(v___x_818_, 0, v___x_828_);
                    v___x_830_ = v___x_818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
                    v___x_830_ = v_reuseFailAlloc_831_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_830_;
            }
            5 => {
                return v___x_836_;
            }
            6 => {
                if v_isShared_842_ == 0 {
                    v___x_844_ = v___x_841_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
                    v___x_844_ = v_reuseFailAlloc_845_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_844_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_getCtorArity_x3f___boxed(
    mut v_declName_847_: *mut leanh::LeanObject,
    mut v_a_848_: *mut leanh::LeanObject,
    mut v_a_849_: *mut leanh::LeanObject,
    mut v_a_850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Lean_Compiler_LCNF_getCtorArity_x3f(v_declName_847_, v_a_848_, v_a_849_);
    leanh::lean_dec(v_a_849_);
    leanh::lean_dec_ref(v_a_848_);
    return v_res_851_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0(
    mut v_00_u03b1_852_: *mut leanh::LeanObject,
    mut v_constName_853_: *mut leanh::LeanObject,
    mut v___y_854_: *mut leanh::LeanObject,
    mut v___y_855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(v_constName_853_, v___y_854_, v___y_855_);
    return v___x_857_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_858_: *mut leanh::LeanObject,
    mut v_constName_859_: *mut leanh::LeanObject,
    mut v___y_860_: *mut leanh::LeanObject,
    mut v___y_861_: *mut leanh::LeanObject,
    mut v___y_862_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0(v_00_u03b1_858_, v_constName_859_, v___y_860_, v___y_861_);
    leanh::lean_dec(v___y_861_);
    leanh::lean_dec_ref(v___y_860_);
    return v_res_863_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_864_: *mut leanh::LeanObject,
    mut v_ref_865_: *mut leanh::LeanObject,
    mut v_constName_866_: *mut leanh::LeanObject,
    mut v___y_867_: *mut leanh::LeanObject,
    mut v___y_868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(v_ref_865_, v_constName_866_, v___y_867_, v___y_868_);
    return v___x_870_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_871_: *mut leanh::LeanObject,
    mut v_ref_872_: *mut leanh::LeanObject,
    mut v_constName_873_: *mut leanh::LeanObject,
    mut v___y_874_: *mut leanh::LeanObject,
    mut v___y_875_: *mut leanh::LeanObject,
    mut v___y_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1(v_00_u03b1_871_, v_ref_872_, v_constName_873_, v___y_874_, v___y_875_);
    leanh::lean_dec(v___y_875_);
    leanh::lean_dec_ref(v___y_874_);
    leanh::lean_dec(v_ref_872_);
    return v_res_877_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_878_: *mut leanh::LeanObject,
    mut v_ref_879_: *mut leanh::LeanObject,
    mut v_msg_880_: *mut leanh::LeanObject,
    mut v_declHint_881_: *mut leanh::LeanObject,
    mut v___y_882_: *mut leanh::LeanObject,
    mut v___y_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_879_, v_msg_880_, v_declHint_881_, v___y_882_, v___y_883_);
    return v___x_885_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_886_: *mut leanh::LeanObject,
    mut v_ref_887_: *mut leanh::LeanObject,
    mut v_msg_888_: *mut leanh::LeanObject,
    mut v_declHint_889_: *mut leanh::LeanObject,
    mut v___y_890_: *mut leanh::LeanObject,
    mut v___y_891_: *mut leanh::LeanObject,
    mut v___y_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_893_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_886_, v_ref_887_, v_msg_888_, v_declHint_889_, v___y_890_, v___y_891_);
    leanh::lean_dec(v___y_891_);
    leanh::lean_dec_ref(v___y_890_);
    leanh::lean_dec(v_ref_887_);
    return v_res_893_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_894_: *mut leanh::LeanObject,
    mut v_declHint_895_: *mut leanh::LeanObject,
    mut v___y_896_: *mut leanh::LeanObject,
    mut v___y_897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_894_, v_declHint_895_, v___y_897_);
    return v___x_899_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_900_: *mut leanh::LeanObject,
    mut v_declHint_901_: *mut leanh::LeanObject,
    mut v___y_902_: *mut leanh::LeanObject,
    mut v___y_903_: *mut leanh::LeanObject,
    mut v___y_904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_900_, v_declHint_901_, v___y_902_, v___y_903_);
    leanh::lean_dec(v___y_903_);
    leanh::lean_dec_ref(v___y_902_);
    return v_res_905_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_906_: *mut leanh::LeanObject,
    mut v_ref_907_: *mut leanh::LeanObject,
    mut v_msg_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_907_, v_msg_908_, v___y_909_, v___y_910_);
    return v___x_912_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_913_: *mut leanh::LeanObject,
    mut v_ref_914_: *mut leanh::LeanObject,
    mut v_msg_915_: *mut leanh::LeanObject,
    mut v___y_916_: *mut leanh::LeanObject,
    mut v___y_917_: *mut leanh::LeanObject,
    mut v___y_918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_919_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_913_, v_ref_914_, v_msg_915_, v___y_916_, v___y_917_);
    leanh::lean_dec(v___y_917_);
    leanh::lean_dec_ref(v___y_916_);
    leanh::lean_dec(v_ref_914_);
    return v_res_919_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_920_: *mut leanh::LeanObject,
    mut v_msg_921_: *mut leanh::LeanObject,
    mut v___y_922_: *mut leanh::LeanObject,
    mut v___y_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_921_, v___y_922_, v___y_923_);
    return v___x_925_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_926_: *mut leanh::LeanObject,
    mut v_msg_927_: *mut leanh::LeanObject,
    mut v___y_928_: *mut leanh::LeanObject,
    mut v___y_929_: *mut leanh::LeanObject,
    mut v___y_930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_926_, v_msg_927_, v___y_928_, v___y_929_);
    leanh::lean_dec(v___y_929_);
    leanh::lean_dec_ref(v___y_928_);
    return v_res_931_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0_spec__0(
    mut v_a_1010_: *mut leanh::LeanObject,
    mut v_as_1011_: *mut leanh::LeanObject,
    mut v_i_1012_: usize,
    mut v_stop_1013_: usize,
) -> u8 {
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: u8 = 0;
    let mut v___x_1017_: usize = 0;
    let mut v___x_1018_: usize = 0;
    let mut v___x_1020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1014_ = lean_usize_dec_eq(v_i_1012_, v_stop_1013_);
                if v___x_1014_ == 0 {
                    v___x_1015_ = lean_array_uget_borrowed(v_as_1011_, v_i_1012_);
                    v___x_1016_ = lean_name_eq(v_a_1010_, v___x_1015_);
                    if v___x_1016_ == 0 {
                        v___x_1017_ = 1usize;
                        v___x_1018_ = lean_usize_add(v_i_1012_, v___x_1017_);
                        v_i_1012_ = v___x_1018_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1016_;
                    }
                } else {
                    v___x_1020_ = 0;
                    return v___x_1020_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0_spec__0___boxed(
    mut v_a_1021_: *mut leanh::LeanObject,
    mut v_as_1022_: *mut leanh::LeanObject,
    mut v_i_1023_: *mut leanh::LeanObject,
    mut v_stop_1024_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1025_: usize = 0;
    let mut v_stop_boxed_1026_: usize = 0;
    let mut v_res_1027_: u8 = 0;
    let mut v_r_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1025_ = leanh::lean_unbox_usize(v_i_1023_);
    leanh::lean_dec(v_i_1023_);
    v_stop_boxed_1026_ = leanh::lean_unbox_usize(v_stop_1024_);
    leanh::lean_dec(v_stop_1024_);
    v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0_spec__0(v_a_1021_, v_as_1022_, v_i_boxed_1025_, v_stop_boxed_1026_);
    leanh::lean_dec_ref(v_as_1022_);
    leanh::lean_dec(v_a_1021_);
    v_r_1028_ = leanh::lean_box((v_res_1027_) as usize);
    return v_r_1028_;
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0(
    mut v_as_1029_: *mut leanh::LeanObject,
    mut v_a_1030_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    v___x_1031_ = leanh::lean_unsigned_to_nat(0);
    v___x_1032_ = lean_array_get_size(v_as_1029_);
    v___x_1033_ = lean_nat_dec_lt(v___x_1031_, v___x_1032_);
    if v___x_1033_ == 0 {
        return v___x_1033_;
    } else {
        if v___x_1033_ == 0 {
            return v___x_1033_;
        } else {
            let mut v___x_1034_: usize = 0;
            let mut v___x_1035_: usize = 0;
            let mut v___x_1036_: u8 = 0;
            v___x_1034_ = 0usize;
            v___x_1035_ = lean_usize_of_nat(v___x_1032_);
            v___x_1036_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0_spec__0(v_a_1030_, v_as_1029_, v___x_1034_, v___x_1035_);
            return v___x_1036_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0___boxed(
    mut v_as_1037_: *mut leanh::LeanObject,
    mut v_a_1038_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1039_: u8 = 0;
    let mut v_r_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0(
        v_as_1037_, v_a_1038_,
    );
    leanh::lean_dec(v_a_1038_);
    leanh::lean_dec_ref(v_as_1037_);
    v_r_1040_ = leanh::lean_box((v_res_1039_) as usize);
    return v_r_1040_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isRuntimeBuiltinType(
    mut v_declName_1041_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    v___x_1042_ = l_Lean_Compiler_LCNF_builtinRuntimeTypes;
    v___x_1043_ = l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0(
        v___x_1042_,
        v_declName_1041_,
    );
    return v___x_1043_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isRuntimeBuiltinType___boxed(
    mut v_declName_1044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1045_: u8 = 0;
    let mut v_r_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_declName_1044_);
    leanh::lean_dec(v_declName_1044_);
    v_r_1046_ = leanh::lean_box((v_res_1045_) as usize);
    return v_r_1046_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Util(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_FloatArray_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Util(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Util(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_FloatArray_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Recognizers(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Util(builtin);
}