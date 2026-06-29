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
pub static l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_isLcCast_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            9297529361438902301 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__0_value)
            as *mut crate::leanh::LeanObject,
        3136308715950998022 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15764114953608429200 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__4_value)
            as *mut crate::leanh::LeanObject,
        9755723410228041222 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__6_value)
            as *mut crate::leanh::LeanObject,
        13474504806189678690 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__8_value)
            as *mut crate::leanh::LeanObject,
        2954612489107370298 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__10_value)
            as *mut crate::leanh::LeanObject,
        17712594561405737325 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__12_value)
            as *mut crate::leanh::LeanObject,
        4889978610488853816 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__14_value)
            as *mut crate::leanh::LeanObject,
        16690552700474419446 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__16_value)
            as *mut crate::leanh::LeanObject,
        15912191227757008981 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__18_value)
            as *mut crate::leanh::LeanObject,
        1347124975762375613 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__20_value)
            as *mut crate::leanh::LeanObject,
        8749134177695247953 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__22_value)
            as *mut crate::leanh::LeanObject,
        14803615792343879184 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24_value:
    crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__24_value)
            as *mut crate::leanh::LeanObject,
        2130556170951526559 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__26_value)
            as *mut crate::leanh::LeanObject,
        11442535297760353691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__28_value)
            as *mut crate::leanh::LeanObject,
        7009148538150066493 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30_value:
    crate::leanh::LeanArrayObject<15> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 15) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 15,
    m_capacity: 15,
    m_data: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__5_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__7_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__9_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__11_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__13_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__15_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__17_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__19_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__21_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__23_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__25_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__27_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__29_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_builtinRuntimeTypes: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinRuntimeTypes___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_isCompilerRelevantMData(
    mut v___mdata_524_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_525_: u8 = 0;
    v___x_525_ = 0;
    return v___x_525_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isCompilerRelevantMData___boxed(
    mut v___mdata_526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_527_: u8 = 0;
    let mut v_r_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_527_ = l_Lean_Compiler_LCNF_isCompilerRelevantMData(v___mdata_526_);
    crate::leanh::lean_dec(v___mdata_526_);
    v_r_528_ = crate::leanh::lean_box((v_res_527_) as usize);
    return v_r_528_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isLcCast_x3f(
    mut v_e_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    v___x_533_ = l_Lean_Compiler_LCNF_isLcCast_x3f___closed__1;
    v___x_534_ = crate::leanh::lean_unsigned_to_nat(3);
    v___x_535_ = l_Lean_Expr_isAppOfArity(v_e_532_, v___x_533_, v___x_534_);
    if v___x_535_ == 0 {
        let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_536_ = crate::leanh::lean_box(0);
        return v___x_536_;
    } else {
        let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_537_ = l_Lean_Expr_appArg_x21(v_e_532_);
        v___x_538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_538_, 0, v___x_537_);
        return v___x_538_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_isLcCast_x3f___boxed(
    mut v_e_539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_540_ = l_Lean_Compiler_LCNF_isLcCast_x3f(v_e_539_);
    crate::leanh::lean_dec_ref(v_e_539_);
    return v_res_540_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_541_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_541_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_542_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0);
    v___x_543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_542_);
    return v___x_543_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_545_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_546_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_546_, 0, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_546_, 1, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_546_, 2, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_546_, 3, v___x_545_);
    crate::leanh::lean_ctor_set(v___x_546_, 4, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_546_, 5, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_546_, 6, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_546_, 7, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_546_, 8, v___x_544_);
    crate::leanh::lean_ctor_set(v___x_546_, 9, v___x_544_);
    return v___x_546_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
    v___x_549_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_549_, 0, v___x_548_);
    return v___x_549_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_550_: usize = 0;
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_550_ = 5usize;
    v___x_551_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_552_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_553_ = lean_mk_empty_array_with_capacity(v___x_552_);
    v___x_554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3);
    v___x_555_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_555_, 0, v___x_554_);
    crate::leanh::lean_ctor_set(v___x_555_, 1, v___x_553_);
    crate::leanh::lean_ctor_set(v___x_555_, 2, v___x_551_);
    crate::leanh::lean_ctor_set(v___x_555_, 3, v___x_551_);
    crate::leanh::lean_ctor_set_usize(v___x_555_, 4, v___x_550_);
    return v___x_555_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = crate::leanh::lean_box(1);
    v___x_557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4);
    v___x_558_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_559_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_559_, 0, v___x_558_);
    crate::leanh::lean_ctor_set(v___x_559_, 1, v___x_557_);
    crate::leanh::lean_ctor_set(v___x_559_, 2, v___x_556_);
    return v___x_559_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = lean_st_ref_get(v___y_562_);
    v_env_565_ = crate::leanh::lean_ctor_get(v___x_564_, 0);
    crate::leanh::lean_inc_ref(v_env_565_);
    crate::leanh::lean_dec(v___x_564_);
    v_options_566_ = crate::leanh::lean_ctor_get(v___y_561_, 2);
    v___x_567_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
    v___x_568_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5);
    crate::leanh::lean_inc_ref(v_options_566_);
    v___x_569_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_569_, 0, v_env_565_);
    crate::leanh::lean_ctor_set(v___x_569_, 1, v___x_567_);
    crate::leanh::lean_ctor_set(v___x_569_, 2, v___x_568_);
    crate::leanh::lean_ctor_set(v___x_569_, 3, v_options_566_);
    v___x_570_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_570_, 0, v___x_569_);
    crate::leanh::lean_ctor_set(v___x_570_, 1, v_msgData_560_);
    v___x_571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_571_, 0, v___x_570_);
    return v___x_571_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
    mut v___y_574_: *mut crate::leanh::LeanObject,
    mut v___y_575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_576_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_572_, v___y_573_, v___y_574_);
    crate::leanh::lean_dec(v___y_574_);
    crate::leanh::lean_dec_ref(v___y_573_);
    return v_res_576_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_577_: *mut crate::leanh::LeanObject,
    mut v___y_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_591_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_581_ = crate::leanh::lean_ctor_get(v___y_578_, 5);
                v___x_582_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_577_, v___y_578_, v___y_579_);
                v_a_583_ = crate::leanh::lean_ctor_get(v___x_582_, 0);
                v_isSharedCheck_591_ = (!crate::leanh::lean_is_exclusive(v___x_582_)) as u8;
                if v_isSharedCheck_591_ == 0 {
                    v___x_585_ = v___x_582_;
                    v_isShared_586_ = v_isSharedCheck_591_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_583_);
                    crate::leanh::lean_dec(v___x_582_);
                    v___x_585_ = crate::leanh::lean_box(0);
                    v_isShared_586_ = v_isSharedCheck_591_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_581_);
                v___x_587_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_587_, 0, v_ref_581_);
                crate::leanh::lean_ctor_set(v___x_587_, 1, v_a_583_);
                if v_isShared_586_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_585_, 1);
                    crate::leanh::lean_ctor_set(v___x_585_, 0, v___x_587_);
                    v___x_589_ = v___x_585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
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
    mut v_msg_592_: *mut crate::leanh::LeanObject,
    mut v___y_593_: *mut crate::leanh::LeanObject,
    mut v___y_594_: *mut crate::leanh::LeanObject,
    mut v___y_595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_596_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_592_, v___y_593_, v___y_594_);
    crate::leanh::lean_dec(v___y_594_);
    crate::leanh::lean_dec_ref(v___y_593_);
    return v_res_596_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_597_: *mut crate::leanh::LeanObject,
    mut v_msg_598_: *mut crate::leanh::LeanObject,
    mut v___y_599_: *mut crate::leanh::LeanObject,
    mut v___y_600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_614_: u8 = 0;
    let mut v_cancelTk_x3f_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_616_: u8 = 0;
    let mut v_inheritedTraceOptions_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_602_ = crate::leanh::lean_ctor_get(v___y_599_, 0);
    v_fileMap_603_ = crate::leanh::lean_ctor_get(v___y_599_, 1);
    v_options_604_ = crate::leanh::lean_ctor_get(v___y_599_, 2);
    v_currRecDepth_605_ = crate::leanh::lean_ctor_get(v___y_599_, 3);
    v_maxRecDepth_606_ = crate::leanh::lean_ctor_get(v___y_599_, 4);
    v_ref_607_ = crate::leanh::lean_ctor_get(v___y_599_, 5);
    v_currNamespace_608_ = crate::leanh::lean_ctor_get(v___y_599_, 6);
    v_openDecls_609_ = crate::leanh::lean_ctor_get(v___y_599_, 7);
    v_initHeartbeats_610_ = crate::leanh::lean_ctor_get(v___y_599_, 8);
    v_maxHeartbeats_611_ = crate::leanh::lean_ctor_get(v___y_599_, 9);
    v_quotContext_612_ = crate::leanh::lean_ctor_get(v___y_599_, 10);
    v_currMacroScope_613_ = crate::leanh::lean_ctor_get(v___y_599_, 11);
    v_diag_614_ = crate::leanh::lean_ctor_get_uint8(
        v___y_599_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_615_ = crate::leanh::lean_ctor_get(v___y_599_, 12);
    v_suppressElabErrors_616_ = crate::leanh::lean_ctor_get_uint8(
        v___y_599_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_617_ = crate::leanh::lean_ctor_get(v___y_599_, 13);
    v_ref_618_ = l_Lean_replaceRef(v_ref_597_, v_ref_607_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_617_);
    crate::leanh::lean_inc(v_cancelTk_x3f_615_);
    crate::leanh::lean_inc(v_currMacroScope_613_);
    crate::leanh::lean_inc(v_quotContext_612_);
    crate::leanh::lean_inc(v_maxHeartbeats_611_);
    crate::leanh::lean_inc(v_initHeartbeats_610_);
    crate::leanh::lean_inc(v_openDecls_609_);
    crate::leanh::lean_inc(v_currNamespace_608_);
    crate::leanh::lean_inc(v_maxRecDepth_606_);
    crate::leanh::lean_inc(v_currRecDepth_605_);
    crate::leanh::lean_inc_ref(v_options_604_);
    crate::leanh::lean_inc_ref(v_fileMap_603_);
    crate::leanh::lean_inc_ref(v_fileName_602_);
    v___x_619_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_619_, 0, v_fileName_602_);
    crate::leanh::lean_ctor_set(v___x_619_, 1, v_fileMap_603_);
    crate::leanh::lean_ctor_set(v___x_619_, 2, v_options_604_);
    crate::leanh::lean_ctor_set(v___x_619_, 3, v_currRecDepth_605_);
    crate::leanh::lean_ctor_set(v___x_619_, 4, v_maxRecDepth_606_);
    crate::leanh::lean_ctor_set(v___x_619_, 5, v_ref_618_);
    crate::leanh::lean_ctor_set(v___x_619_, 6, v_currNamespace_608_);
    crate::leanh::lean_ctor_set(v___x_619_, 7, v_openDecls_609_);
    crate::leanh::lean_ctor_set(v___x_619_, 8, v_initHeartbeats_610_);
    crate::leanh::lean_ctor_set(v___x_619_, 9, v_maxHeartbeats_611_);
    crate::leanh::lean_ctor_set(v___x_619_, 10, v_quotContext_612_);
    crate::leanh::lean_ctor_set(v___x_619_, 11, v_currMacroScope_613_);
    crate::leanh::lean_ctor_set(v___x_619_, 12, v_cancelTk_x3f_615_);
    crate::leanh::lean_ctor_set(v___x_619_, 13, v_inheritedTraceOptions_617_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_619_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_614_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_619_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_616_,
    );
    v___x_620_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_598_, v___x_619_, v___y_600_);
    crate::leanh::lean_dec_ref_known(v___x_619_, 14);
    return v___x_620_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_621_: *mut crate::leanh::LeanObject,
    mut v_msg_622_: *mut crate::leanh::LeanObject,
    mut v___y_623_: *mut crate::leanh::LeanObject,
    mut v___y_624_: *mut crate::leanh::LeanObject,
    mut v___y_625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_621_, v_msg_622_, v___y_623_, v___y_624_);
    crate::leanh::lean_dec(v___y_624_);
    crate::leanh::lean_dec_ref(v___y_623_);
    crate::leanh::lean_dec(v_ref_621_);
    return v_res_626_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_628_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_629_ = l_Lean_stringToMessageData(v___x_628_);
    return v___x_629_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_632_ = l_Lean_stringToMessageData(v___x_631_);
    return v___x_632_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_634_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_635_ = l_Lean_stringToMessageData(v___x_634_);
    return v___x_635_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_638_ = l_Lean_stringToMessageData(v___x_637_);
    return v___x_638_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
    return v___x_641_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_643_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
    return v___x_644_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_646_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
    return v___x_647_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_648_: *mut crate::leanh::LeanObject,
    mut v_declHint_649_: *mut crate::leanh::LeanObject,
    mut v___y_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_654_: u8 = 0;
    let mut v_isExporting_655_: u8 = 0;
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: u8 = 0;
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_709_: u8 = 0;
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_652_ = lean_st_ref_get(v___y_650_);
                v_env_653_ = crate::leanh::lean_ctor_get(v___x_652_, 0);
                crate::leanh::lean_inc_ref(v_env_653_);
                crate::leanh::lean_dec(v___x_652_);
                v___x_654_ = l_Lean_Name_isAnonymous(v_declHint_649_);
                if v___x_654_ == 0 {
                    v_isExporting_655_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_653_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_655_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_653_);
                        crate::leanh::lean_dec(v_declHint_649_);
                        v___x_656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_656_, 0, v_msg_648_);
                        return v___x_656_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_653_);
                        v___x_657_ = l_Lean_Environment_setExporting(v_env_653_, v___x_654_);
                        crate::leanh::lean_inc(v_declHint_649_);
                        crate::leanh::lean_inc_ref(v___x_657_);
                        v___x_658_ = l_Lean_Environment_contains(
                            v___x_657_,
                            v_declHint_649_,
                            v_isExporting_655_,
                        );
                        if v___x_658_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_657_);
                            crate::leanh::lean_dec_ref(v_env_653_);
                            crate::leanh::lean_dec(v_declHint_649_);
                            v___x_659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_659_, 0, v_msg_648_);
                            return v___x_659_;
                        } else {
                            v___x_660_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_661_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5);
                            v___x_662_ = l_Lean_Options_empty;
                            v___x_663_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_663_, 0, v___x_657_);
                            crate::leanh::lean_ctor_set(v___x_663_, 1, v___x_660_);
                            crate::leanh::lean_ctor_set(v___x_663_, 2, v___x_661_);
                            crate::leanh::lean_ctor_set(v___x_663_, 3, v___x_662_);
                            crate::leanh::lean_inc(v_declHint_649_);
                            v___x_664_ =
                                l_Lean_MessageData_ofConstName(v_declHint_649_, v___x_654_);
                            v_c_665_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_665_, 0, v___x_663_);
                            crate::leanh::lean_ctor_set(v_c_665_, 1, v___x_664_);
                            v___x_666_ =
                                l_Lean_Environment_getModuleIdxFor_x3f(v_env_653_, v_declHint_649_);
                            if crate::leanh::lean_obj_tag(v___x_666_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_653_);
                                crate::leanh::lean_dec(v_declHint_649_);
                                v___x_667_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_668_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
                                crate::leanh::lean_ctor_set(v___x_668_, 1, v_c_665_);
                                v___x_669_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_670_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_670_, 0, v___x_668_);
                                crate::leanh::lean_ctor_set(v___x_670_, 1, v___x_669_);
                                v___x_671_ = l_Lean_MessageData_note(v___x_670_);
                                v___x_672_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_672_, 0, v_msg_648_);
                                crate::leanh::lean_ctor_set(v___x_672_, 1, v___x_671_);
                                v___x_673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_673_, 0, v___x_672_);
                                return v___x_673_;
                            } else {
                                v_val_674_ = crate::leanh::lean_ctor_get(v___x_666_, 0);
                                v_isSharedCheck_709_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_666_)) as u8;
                                if v_isSharedCheck_709_ == 0 {
                                    v___x_676_ = v___x_666_;
                                    v_isShared_677_ = v_isSharedCheck_709_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_674_);
                                    crate::leanh::lean_dec(v___x_666_);
                                    v___x_676_ = crate::leanh::lean_box(0);
                                    v_isShared_677_ = v_isSharedCheck_709_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_653_);
                    crate::leanh::lean_dec(v_declHint_649_);
                    v___x_710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_710_, 0, v_msg_648_);
                    return v___x_710_;
                }
            }
            1 => {
                v___x_678_ = crate::leanh::lean_box(0);
                v___x_679_ = l_Lean_Environment_header(v_env_653_);
                crate::leanh::lean_dec_ref(v_env_653_);
                v___x_680_ = l_Lean_EnvironmentHeader_moduleNames(v___x_679_);
                v_mod_681_ = lean_array_get(v___x_678_, v___x_680_, v_val_674_);
                crate::leanh::lean_dec(v_val_674_);
                crate::leanh::lean_dec_ref(v___x_680_);
                v___x_682_ = l_Lean_isPrivateName(v_declHint_649_);
                crate::leanh::lean_dec(v_declHint_649_);
                if v___x_682_ == 0 {
                    v___x_683_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_684_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_684_, 0, v___x_683_);
                    crate::leanh::lean_ctor_set(v___x_684_, 1, v_c_665_);
                    v___x_685_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_686_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_686_, 0, v___x_684_);
                    crate::leanh::lean_ctor_set(v___x_686_, 1, v___x_685_);
                    v___x_687_ = l_Lean_MessageData_ofName(v_mod_681_);
                    v___x_688_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_688_, 0, v___x_686_);
                    crate::leanh::lean_ctor_set(v___x_688_, 1, v___x_687_);
                    v___x_689_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_690_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_690_, 0, v___x_688_);
                    crate::leanh::lean_ctor_set(v___x_690_, 1, v___x_689_);
                    v___x_691_ = l_Lean_MessageData_note(v___x_690_);
                    v___x_692_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_692_, 0, v_msg_648_);
                    crate::leanh::lean_ctor_set(v___x_692_, 1, v___x_691_);
                    if v_isShared_677_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_676_, 0);
                        crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_692_);
                        v___x_694_ = v___x_676_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_695_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
                        v___x_694_ = v_reuseFailAlloc_695_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_697_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_697_, 0, v___x_696_);
                    crate::leanh::lean_ctor_set(v___x_697_, 1, v_c_665_);
                    v___x_698_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_699_, 0, v___x_697_);
                    crate::leanh::lean_ctor_set(v___x_699_, 1, v___x_698_);
                    v___x_700_ = l_Lean_MessageData_ofName(v_mod_681_);
                    v___x_701_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_701_, 0, v___x_699_);
                    crate::leanh::lean_ctor_set(v___x_701_, 1, v___x_700_);
                    v___x_702_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_703_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_703_, 0, v___x_701_);
                    crate::leanh::lean_ctor_set(v___x_703_, 1, v___x_702_);
                    v___x_704_ = l_Lean_MessageData_note(v___x_703_);
                    v___x_705_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_705_, 0, v_msg_648_);
                    crate::leanh::lean_ctor_set(v___x_705_, 1, v___x_704_);
                    if v_isShared_677_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_676_, 0);
                        crate::leanh::lean_ctor_set(v___x_676_, 0, v___x_705_);
                        v___x_707_ = v___x_676_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_708_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_708_, 0, v___x_705_);
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
    mut v_msg_711_: *mut crate::leanh::LeanObject,
    mut v_declHint_712_: *mut crate::leanh::LeanObject,
    mut v___y_713_: *mut crate::leanh::LeanObject,
    mut v___y_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_715_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_711_, v_declHint_712_, v___y_713_);
    crate::leanh::lean_dec(v___y_713_);
    return v_res_715_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_716_: *mut crate::leanh::LeanObject,
    mut v_declHint_717_: *mut crate::leanh::LeanObject,
    mut v___y_718_: *mut crate::leanh::LeanObject,
    mut v___y_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_725_: u8 = 0;
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_721_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_716_, v_declHint_717_, v___y_719_);
                v_a_722_ = crate::leanh::lean_ctor_get(v___x_721_, 0);
                v_isSharedCheck_731_ = (!crate::leanh::lean_is_exclusive(v___x_721_)) as u8;
                if v_isSharedCheck_731_ == 0 {
                    v___x_724_ = v___x_721_;
                    v_isShared_725_ = v_isSharedCheck_731_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_722_);
                    crate::leanh::lean_dec(v___x_721_);
                    v___x_724_ = crate::leanh::lean_box(0);
                    v_isShared_725_ = v_isSharedCheck_731_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_726_ = l_Lean_unknownIdentifierMessageTag;
                v___x_727_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_727_, 0, v___x_726_);
                crate::leanh::lean_ctor_set(v___x_727_, 1, v_a_722_);
                if v_isShared_725_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_724_, 0, v___x_727_);
                    v___x_729_ = v___x_724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_730_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
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
    mut v_msg_732_: *mut crate::leanh::LeanObject,
    mut v_declHint_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
    mut v___y_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_737_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_732_, v_declHint_733_, v___y_734_, v___y_735_);
    crate::leanh::lean_dec(v___y_735_);
    crate::leanh::lean_dec_ref(v___y_734_);
    return v_res_737_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_738_: *mut crate::leanh::LeanObject,
    mut v_msg_739_: *mut crate::leanh::LeanObject,
    mut v_declHint_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_739_, v_declHint_740_, v___y_741_, v___y_742_);
    v_a_745_ = crate::leanh::lean_ctor_get(v___x_744_, 0);
    crate::leanh::lean_inc(v_a_745_);
    crate::leanh::lean_dec_ref(v___x_744_);
    v___x_746_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_738_, v_a_745_, v___y_741_, v___y_742_);
    return v___x_746_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_747_: *mut crate::leanh::LeanObject,
    mut v_msg_748_: *mut crate::leanh::LeanObject,
    mut v_declHint_749_: *mut crate::leanh::LeanObject,
    mut v___y_750_: *mut crate::leanh::LeanObject,
    mut v___y_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_753_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_747_, v_msg_748_, v_declHint_749_, v___y_750_, v___y_751_);
    crate::leanh::lean_dec(v___y_751_);
    crate::leanh::lean_dec_ref(v___y_750_);
    crate::leanh::lean_dec(v_ref_747_);
    return v_res_753_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_755_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_756_ = l_Lean_stringToMessageData(v___x_755_);
    return v___x_756_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_758_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_759_ = l_Lean_stringToMessageData(v___x_758_);
    return v___x_759_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_ref_760_: *mut crate::leanh::LeanObject,
    mut v_constName_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_765_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_766_ = 0;
    crate::leanh::lean_inc(v_constName_761_);
    v___x_767_ = l_Lean_MessageData_ofConstName(v_constName_761_, v___x_766_);
    v___x_768_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_768_, 0, v___x_765_);
    crate::leanh::lean_ctor_set(v___x_768_, 1, v___x_767_);
    v___x_769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_770_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_770_, 0, v___x_768_);
    crate::leanh::lean_ctor_set(v___x_770_, 1, v___x_769_);
    v___x_771_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_760_, v___x_770_, v_constName_761_, v___y_762_, v___y_763_);
    return v___x_771_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_772_: *mut crate::leanh::LeanObject,
    mut v_constName_773_: *mut crate::leanh::LeanObject,
    mut v___y_774_: *mut crate::leanh::LeanObject,
    mut v___y_775_: *mut crate::leanh::LeanObject,
    mut v___y_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_777_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(v_ref_772_, v_constName_773_, v___y_774_, v___y_775_);
    crate::leanh::lean_dec(v___y_775_);
    crate::leanh::lean_dec_ref(v___y_774_);
    crate::leanh::lean_dec(v_ref_772_);
    return v_res_777_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(
    mut v_constName_778_: *mut crate::leanh::LeanObject,
    mut v___y_779_: *mut crate::leanh::LeanObject,
    mut v___y_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_782_ = crate::leanh::lean_ctor_get(v___y_779_, 5);
    v___x_783_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(v_ref_782_, v_constName_778_, v___y_779_, v___y_780_);
    return v___x_783_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg___boxed(
    mut v_constName_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_788_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(v_constName_784_, v___y_785_, v___y_786_);
    crate::leanh::lean_dec(v___y_786_);
    crate::leanh::lean_dec_ref(v___y_785_);
    return v_res_788_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0(
    mut v_constName_789_: *mut crate::leanh::LeanObject,
    mut v___y_790_: *mut crate::leanh::LeanObject,
    mut v___y_791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: u8 = 0;
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_801_: u8 = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_793_ = lean_st_ref_get(v___y_791_);
                v_env_794_ = crate::leanh::lean_ctor_get(v___x_793_, 0);
                crate::leanh::lean_inc_ref(v_env_794_);
                crate::leanh::lean_dec(v___x_793_);
                v___x_795_ = 0;
                crate::leanh::lean_inc(v_constName_789_);
                v___x_796_ = l_Lean_Environment_find_x3f(v_env_794_, v_constName_789_, v___x_795_);
                if crate::leanh::lean_obj_tag(v___x_796_) == 0 {
                    v___x_797_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(v_constName_789_, v___y_790_, v___y_791_);
                    return v___x_797_;
                } else {
                    crate::leanh::lean_dec(v_constName_789_);
                    v_val_798_ = crate::leanh::lean_ctor_get(v___x_796_, 0);
                    v_isSharedCheck_805_ = (!crate::leanh::lean_is_exclusive(v___x_796_)) as u8;
                    if v_isSharedCheck_805_ == 0 {
                        v___x_800_ = v___x_796_;
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_798_);
                        crate::leanh::lean_dec(v___x_796_);
                        v___x_800_ = crate::leanh::lean_box(0);
                        v_isShared_801_ = v_isSharedCheck_805_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_801_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_800_, 0);
                    v___x_803_ = v___x_800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_804_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_804_, 0, v_val_798_);
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
    mut v_constName_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_810_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0(
        v_constName_806_,
        v___y_807_,
        v___y_808_,
    );
    crate::leanh::lean_dec(v___y_808_);
    crate::leanh::lean_dec_ref(v___y_807_);
    return v_res_810_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getCtorArity_x3f(
    mut v_declName_811_: *mut crate::leanh::LeanObject,
    mut v_a_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v_val_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_823_: u8 = 0;
    let mut v_numParams_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFields_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_838_: u8 = 0;
    let mut v_a_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_842_: u8 = 0;
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                if crate::leanh::lean_obj_tag(v___x_815_) == 0 {
                    v_a_816_ = crate::leanh::lean_ctor_get(v___x_815_, 0);
                    v_isSharedCheck_838_ = (!crate::leanh::lean_is_exclusive(v___x_815_)) as u8;
                    if v_isSharedCheck_838_ == 0 {
                        v___x_818_ = v___x_815_;
                        v_isShared_819_ = v_isSharedCheck_838_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_816_);
                        crate::leanh::lean_dec(v___x_815_);
                        v___x_818_ = crate::leanh::lean_box(0);
                        v_isShared_819_ = v_isSharedCheck_838_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_839_ = crate::leanh::lean_ctor_get(v___x_815_, 0);
                    v_isSharedCheck_846_ = (!crate::leanh::lean_is_exclusive(v___x_815_)) as u8;
                    if v_isSharedCheck_846_ == 0 {
                        v___x_841_ = v___x_815_;
                        v_isShared_842_ = v_isSharedCheck_846_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_839_);
                        crate::leanh::lean_dec(v___x_815_);
                        v___x_841_ = crate::leanh::lean_box(0);
                        v_isShared_842_ = v_isSharedCheck_846_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_816_) == 6 {
                    v_val_820_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                    v_isSharedCheck_833_ = (!crate::leanh::lean_is_exclusive(v_a_816_)) as u8;
                    if v_isSharedCheck_833_ == 0 {
                        v___x_822_ = v_a_816_;
                        v_isShared_823_ = v_isSharedCheck_833_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_820_);
                        crate::leanh::lean_dec(v_a_816_);
                        v___x_822_ = crate::leanh::lean_box(0);
                        v_isShared_823_ = v_isSharedCheck_833_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_816_);
                    v___x_834_ = crate::leanh::lean_box(0);
                    if v_isShared_819_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_818_, 0, v___x_834_);
                        v___x_836_ = v___x_818_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_837_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
                        v___x_836_ = v_reuseFailAlloc_837_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_numParams_824_ = crate::leanh::lean_ctor_get(v_val_820_, 3);
                crate::leanh::lean_inc(v_numParams_824_);
                v_numFields_825_ = crate::leanh::lean_ctor_get(v_val_820_, 4);
                crate::leanh::lean_inc(v_numFields_825_);
                crate::leanh::lean_dec_ref(v_val_820_);
                v___x_826_ = lean_nat_add(v_numParams_824_, v_numFields_825_);
                crate::leanh::lean_dec(v_numFields_825_);
                crate::leanh::lean_dec(v_numParams_824_);
                if v_isShared_823_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_822_, 1);
                    crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_826_);
                    v___x_828_ = v___x_822_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_826_);
                    v___x_828_ = v_reuseFailAlloc_832_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_818_, 0, v___x_828_);
                    v___x_830_ = v___x_818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
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
                    v_reuseFailAlloc_845_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
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
    mut v_declName_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Lean_Compiler_LCNF_getCtorArity_x3f(v_declName_847_, v_a_848_, v_a_849_);
    crate::leanh::lean_dec(v_a_849_);
    crate::leanh::lean_dec_ref(v_a_848_);
    return v_res_851_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0(
    mut v_00_u03b1_852_: *mut crate::leanh::LeanObject,
    mut v_constName_853_: *mut crate::leanh::LeanObject,
    mut v___y_854_: *mut crate::leanh::LeanObject,
    mut v___y_855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___redArg(v_constName_853_, v___y_854_, v___y_855_);
    return v___x_857_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b1_858_: *mut crate::leanh::LeanObject,
    mut v_constName_859_: *mut crate::leanh::LeanObject,
    mut v___y_860_: *mut crate::leanh::LeanObject,
    mut v___y_861_: *mut crate::leanh::LeanObject,
    mut v___y_862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_863_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0(v_00_u03b1_858_, v_constName_859_, v___y_860_, v___y_861_);
    crate::leanh::lean_dec(v___y_861_);
    crate::leanh::lean_dec_ref(v___y_860_);
    return v_res_863_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b1_864_: *mut crate::leanh::LeanObject,
    mut v_ref_865_: *mut crate::leanh::LeanObject,
    mut v_constName_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___redArg(v_ref_865_, v_constName_866_, v___y_867_, v___y_868_);
    return v___x_870_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_871_: *mut crate::leanh::LeanObject,
    mut v_ref_872_: *mut crate::leanh::LeanObject,
    mut v_constName_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
    mut v___y_875_: *mut crate::leanh::LeanObject,
    mut v___y_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1(v_00_u03b1_871_, v_ref_872_, v_constName_873_, v___y_874_, v___y_875_);
    crate::leanh::lean_dec(v___y_875_);
    crate::leanh::lean_dec_ref(v___y_874_);
    crate::leanh::lean_dec(v_ref_872_);
    return v_res_877_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_878_: *mut crate::leanh::LeanObject,
    mut v_ref_879_: *mut crate::leanh::LeanObject,
    mut v_msg_880_: *mut crate::leanh::LeanObject,
    mut v_declHint_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
    mut v___y_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_885_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_879_, v_msg_880_, v_declHint_881_, v___y_882_, v___y_883_);
    return v___x_885_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_886_: *mut crate::leanh::LeanObject,
    mut v_ref_887_: *mut crate::leanh::LeanObject,
    mut v_msg_888_: *mut crate::leanh::LeanObject,
    mut v_declHint_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
    mut v___y_891_: *mut crate::leanh::LeanObject,
    mut v___y_892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_893_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_886_, v_ref_887_, v_msg_888_, v_declHint_889_, v___y_890_, v___y_891_);
    crate::leanh::lean_dec(v___y_891_);
    crate::leanh::lean_dec_ref(v___y_890_);
    crate::leanh::lean_dec(v_ref_887_);
    return v_res_893_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_894_: *mut crate::leanh::LeanObject,
    mut v_declHint_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_899_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_894_, v_declHint_895_, v___y_897_);
    return v___x_899_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_900_: *mut crate::leanh::LeanObject,
    mut v_declHint_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_905_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_900_, v_declHint_901_, v___y_902_, v___y_903_);
    crate::leanh::lean_dec(v___y_903_);
    crate::leanh::lean_dec_ref(v___y_902_);
    return v_res_905_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_906_: *mut crate::leanh::LeanObject,
    mut v_ref_907_: *mut crate::leanh::LeanObject,
    mut v_msg_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_912_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_907_, v_msg_908_, v___y_909_, v___y_910_);
    return v___x_912_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_913_: *mut crate::leanh::LeanObject,
    mut v_ref_914_: *mut crate::leanh::LeanObject,
    mut v_msg_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
    mut v___y_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_919_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_913_, v_ref_914_, v_msg_915_, v___y_916_, v___y_917_);
    crate::leanh::lean_dec(v___y_917_);
    crate::leanh::lean_dec_ref(v___y_916_);
    crate::leanh::lean_dec(v_ref_914_);
    return v_res_919_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_920_: *mut crate::leanh::LeanObject,
    mut v_msg_921_: *mut crate::leanh::LeanObject,
    mut v___y_922_: *mut crate::leanh::LeanObject,
    mut v___y_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_925_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_921_, v___y_922_, v___y_923_);
    return v___x_925_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_926_: *mut crate::leanh::LeanObject,
    mut v_msg_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_931_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_getCtorArity_x3f_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_926_, v_msg_927_, v___y_928_, v___y_929_);
    crate::leanh::lean_dec(v___y_929_);
    crate::leanh::lean_dec_ref(v___y_928_);
    return v_res_931_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0_spec__0(
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_as_1011_: *mut crate::leanh::LeanObject,
    mut v_i_1012_: usize,
    mut v_stop_1013_: usize,
) -> u8 {
    let mut v___x_1014_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_a_1021_: *mut crate::leanh::LeanObject,
    mut v_as_1022_: *mut crate::leanh::LeanObject,
    mut v_i_1023_: *mut crate::leanh::LeanObject,
    mut v_stop_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1025_: usize = 0;
    let mut v_stop_boxed_1026_: usize = 0;
    let mut v_res_1027_: u8 = 0;
    let mut v_r_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1025_ = crate::leanh::lean_unbox_usize(v_i_1023_);
    crate::leanh::lean_dec(v_i_1023_);
    v_stop_boxed_1026_ = crate::leanh::lean_unbox_usize(v_stop_1024_);
    crate::leanh::lean_dec(v_stop_1024_);
    v_res_1027_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0_spec__0(v_a_1021_, v_as_1022_, v_i_boxed_1025_, v_stop_boxed_1026_);
    crate::leanh::lean_dec_ref(v_as_1022_);
    crate::leanh::lean_dec(v_a_1021_);
    v_r_1028_ = crate::leanh::lean_box((v_res_1027_) as usize);
    return v_r_1028_;
}
pub unsafe fn l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0(
    mut v_as_1029_: *mut crate::leanh::LeanObject,
    mut v_a_1030_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    v___x_1031_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_as_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1039_: u8 = 0;
    let mut v_r_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1039_ = l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0(
        v_as_1037_, v_a_1038_,
    );
    crate::leanh::lean_dec(v_a_1038_);
    crate::leanh::lean_dec_ref(v_as_1037_);
    v_r_1040_ = crate::leanh::lean_box((v_res_1039_) as usize);
    return v_r_1040_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isRuntimeBuiltinType(
    mut v_declName_1041_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    v___x_1042_ = l_Lean_Compiler_LCNF_builtinRuntimeTypes;
    v___x_1043_ = l_Array_contains___at___00Lean_Compiler_LCNF_isRuntimeBuiltinType_spec__0(
        v___x_1042_,
        v_declName_1041_,
    );
    return v___x_1043_;
}
pub unsafe fn l_Lean_Compiler_LCNF_isRuntimeBuiltinType___boxed(
    mut v_declName_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1045_: u8 = 0;
    let mut v_r_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1045_ = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(v_declName_1044_);
    crate::leanh::lean_dec(v_declName_1044_);
    v_r_1046_ = crate::leanh::lean_box((v_res_1045_) as usize);
    return v_r_1046_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_FloatArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Util(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Util(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_FloatArray_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_CoreM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_Recognizers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Util(builtin);
}
