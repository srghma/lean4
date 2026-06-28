// Lean compiler output
// Module: Lean.Compiler.InlineAttrs
// Imports: Lean.Attributes Lean.Meta.RecExt
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_replaceRef, l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::Attributes::{
    initialize_Lean_Attributes, l_Lean_EnumAttributes_getValue___redArg,
    l_Lean_EnumAttributes_setValue___redArg, l_Lean_registerEnumAttributes___redArg,
    runtime_initialize_Lean_Attributes,
};
use crate::r#gen::Lean::Compiler::Old::l_Lean_Compiler_checkIsDefinition;
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
use crate::r#gen::Lean::Meta::RecExt::{
    initialize_Lean_Meta_RecExt, l_Lean_Meta_isRecursiveDefinition___redArg,
    runtime_initialize_Lean_Meta_RecExt,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_nat_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static mut l_Lean_Compiler_instInhabitedInlineAttributeKind_default: u8 = 0;
pub static mut l_Lean_Compiler_instInhabitedInlineAttributeKind: u8 = 0;
pub static l_Lean_Compiler_instBEqInlineAttributeKind___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_instBEqInlineAttributeKind_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_instBEqInlineAttributeKind___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_instBEqInlineAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_instBEqInlineAttributeKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_instBEqInlineAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_instHashableInlineAttributeKind___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_instHashableInlineAttributeKind_hash___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_instHashableInlineAttributeKind___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_instHashableInlineAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_instHashableInlineAttributeKind: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_instHashableInlineAttributeKind___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__1_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [110, 111, 105, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__2_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [109, 97, 99, 114, 111, 95, 105, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [105, 110, 108, 105, 110, 101, 95, 105, 102, 95, 114, 101, 100, 117, 99, 101, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [97, 108, 119, 97, 121, 115, 95, 105, 110, 108, 105, 110, 101, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 96, 91, 109, 97, 99, 114, 111, 95, 105, 110, 108, 105, 110, 101, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 116, 111, 32, 96, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<106> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [96, 58, 32, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32, 116, 104, 105, 115, 32, 107, 105, 110, 100, 32, 111, 102, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 59, 32, 111, 110, 108, 121, 32, 110, 111, 110, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 115, 32, 97, 114, 101, 32, 115, 117, 112, 112, 111, 114, 116, 101, 100, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 96, 91, 109, 97, 99, 114, 111, 95, 105, 110, 108, 105, 110, 101, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 44, 32, 96, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 97, 110, 32, 101, 120, 112, 111, 115, 101, 100, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [93, 96, 58, 32, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__0_value) as *mut crate::leanh::LeanObject,8159932143332935260 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__3_value) as *mut crate::leanh::LeanObject,14229988309860620923 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<98> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 98, m_capacity: 98, m_length: 97, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 32, 119, 104, 101, 110, 32, 114, 101, 115, 117, 108, 116, 97, 110, 116, 32, 116, 101, 114, 109, 32, 97, 102, 116, 101, 114, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 96, 99, 97, 115, 101, 115, 95, 111, 110, 96, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__1_value) as *mut crate::leanh::LeanObject,18094623486030855 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__11_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__10_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__12_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__2_value) as *mut crate::leanh::LeanObject,4629925702708344642 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<59> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 59, m_capacity: 59, m_length: 58, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 32, 98, 101, 102, 111, 114, 101, 32, 65, 78, 70, 32, 99, 111, 110, 118, 101, 114, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__15_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__14_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__16_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__4_value) as *mut crate::leanh::LeanObject,16165622370258547087 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [109, 97, 114, 107, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 98, 101, 32, 97, 108, 119, 97, 121, 115, 32, 105, 110, 108, 105, 110, 101, 100, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__19_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__18_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__20_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__21_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__17_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__22_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__13_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__23_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__25_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__24_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__25_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__25_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__26_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__25_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__26_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__26_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__27_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__27_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__27_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__28_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__28_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__28_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__29_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 108, 105, 110, 101, 65, 116, 116, 114, 115, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__29_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__29_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__27_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__28_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8543197020067251012 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__29_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3659688833149115581 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1___closed__0_value: crate::leanh::LeanStringObject<923> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 923, m_capacity: 923, m_length: 922, m_data: [67, 104, 97, 110, 103, 101, 115, 32, 116, 104, 101, 32, 105, 110, 108, 105, 110, 105, 110, 103, 32, 98, 101, 104, 97, 118, 105, 111, 114, 46, 32, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 111, 109, 101, 115, 32, 105, 110, 32, 115, 101, 118, 101, 114, 97, 108, 32, 118, 97, 114, 105, 97, 110, 116, 115, 58, 10, 45, 32, 96, 64, 91, 105, 110, 108, 105, 110, 101, 93, 96, 58, 32, 109, 97, 114, 107, 115, 32, 116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 32, 119, 104, 101, 110, 32, 105, 116, 32, 105, 115, 32, 97, 112, 112, 114, 111, 112, 114, 105, 97, 116, 101, 46, 10, 45, 32, 96, 64, 91, 105, 110, 108, 105, 110, 101, 95, 105, 102, 95, 114, 101, 100, 117, 99, 101, 93, 96, 58, 32, 109, 97, 114, 107, 115, 32, 116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 32, 105, 102, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105, 111, 110, 32, 111, 102, 32, 105, 116, 32, 97, 102, 116, 101, 114, 32, 105, 110, 108, 105, 110, 105, 110, 103, 10, 32, 32, 97, 110, 100, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 114, 101, 100, 117, 99, 116, 105, 111, 110, 32, 105, 115, 110, 39, 116, 32, 97, 32, 96, 109, 97, 116, 99, 104, 96, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 46, 32, 84, 104, 105, 115, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 99, 97, 110, 32, 98, 101, 32, 117, 115, 101, 100, 32, 102, 111, 114, 32, 105, 110, 108, 105, 110, 105, 110, 103, 10, 32, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 108, 121, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 46, 10, 45, 32, 96, 64, 91, 110, 111, 105, 110, 108, 105, 110, 101, 93, 96, 58, 32, 109, 97, 114, 107, 115, 32, 116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 110, 101, 118, 101, 114, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 46, 10, 45, 32, 96, 64, 91, 97, 108, 119, 97, 121, 115, 95, 105, 110, 108, 105, 110, 101, 93, 96, 58, 32, 109, 97, 114, 107, 115, 32, 116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 46, 10, 45, 32, 96, 64, 91, 109, 97, 99, 114, 111, 95, 105, 110, 108, 105, 110, 101, 93, 96, 58, 32, 109, 97, 114, 107, 115, 32, 116, 104, 101, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 32, 116, 111, 32, 97, 108, 119, 97, 121, 115, 32, 98, 101, 32, 105, 110, 108, 105, 110, 101, 100, 32, 97, 116, 32, 116, 104, 101, 32, 98, 101, 103, 105, 110, 110, 105, 110, 103, 32, 111, 102, 32, 99, 111, 109, 112, 105, 108, 97, 116, 105, 111, 110, 46, 10, 32, 32, 84, 104, 105, 115, 32, 109, 97, 107, 101, 115, 32, 105, 116, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 116, 111, 32, 100, 101, 102, 105, 110, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 116, 104, 97, 116, 32, 101, 118, 97, 108, 117, 97, 116, 101, 32, 115, 111, 109, 101, 32, 111, 102, 32, 116, 104, 101, 105, 114, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 108, 97, 122, 105, 108, 121, 46, 10, 32, 32, 69, 120, 97, 109, 112, 108, 101, 58, 10, 32, 32, 96, 96, 96, 10, 32, 32, 64, 91, 109, 97, 99, 114, 111, 95, 105, 110, 108, 105, 110, 101, 93, 10, 32, 32, 100, 101, 102, 32, 116, 101, 115, 116, 32, 40, 120, 32, 121, 32, 58, 32, 78, 97, 116, 41, 32, 58, 32, 78, 97, 116, 32, 58, 61, 10, 32, 32, 32, 32, 105, 102, 32, 120, 32, 61, 32, 52, 50, 32, 116, 104, 101, 110, 32, 120, 32, 101, 108, 115, 101, 32, 121, 10, 10, 32, 32, 35, 101, 118, 97, 108, 32, 116, 101, 115, 116, 32, 52, 50, 32, 40, 50, 94, 49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 41, 32, 45, 45, 32, 100, 111, 101, 115, 110, 39, 116, 32, 99, 111, 109, 112, 117, 116, 101, 32, 50, 94, 49, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 48, 10, 32, 32, 96, 96, 96, 10, 32, 32, 79, 110, 108, 121, 32, 110, 111, 110, 45, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 109, 97, 121, 32, 98, 101, 32, 109, 97, 114, 107, 101, 100, 32, 96, 64, 91, 109, 97, 99, 114, 111, 95, 105, 110, 108, 105, 110, 101, 93, 96, 46, 10, 0]};
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 78 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 19 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 30 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_ctorIdx(
    mut v_x_1018_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1018_ {
        0 => {
            let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1019_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1019_;
        }
        1 => {
            let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1020_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_1020_;
        }
        2 => {
            let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1021_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_1021_;
        }
        3 => {
            let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1022_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_1022_;
        }
        _ => {
            let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1023_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_1023_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_ctorIdx___boxed(
    mut v_x_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_boxed_1025_: u8 = 0;
    let mut v_res_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1025_ = (crate::leanh::lean_unbox(v_x_1024_) as u8);
    v_res_1026_ = l_Lean_Compiler_InlineAttributeKind_ctorIdx(v_x_boxed_1025_);
    return v_res_1026_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_toCtorIdx(
    mut v_x_1027_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1028_ = l_Lean_Compiler_InlineAttributeKind_ctorIdx(v_x_1027_);
    return v___x_1028_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_toCtorIdx___boxed(
    mut v_x_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4__boxed_1030_: u8 = 0;
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1030_ = (crate::leanh::lean_unbox(v_x_1029_) as u8);
    v_res_1031_ = l_Lean_Compiler_InlineAttributeKind_toCtorIdx(v_x_4__boxed_1030_);
    return v_res_1031_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_ctorElim___redArg(
    mut v_k_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1032_);
    return v_k_1032_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_ctorElim___redArg___boxed(
    mut v_k_1033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1034_ = l_Lean_Compiler_InlineAttributeKind_ctorElim___redArg(v_k_1033_);
    crate::leanh::lean_dec(v_k_1033_);
    return v_res_1034_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_ctorElim(
    mut v_motive_1035_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1036_: *mut crate::leanh::LeanObject,
    mut v_t_1037_: u8,
    mut v_h_1038_: *mut crate::leanh::LeanObject,
    mut v_k_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_k_1039_);
    return v_k_1039_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_ctorElim___boxed(
    mut v_motive_1040_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1041_: *mut crate::leanh::LeanObject,
    mut v_t_1042_: *mut crate::leanh::LeanObject,
    mut v_h_1043_: *mut crate::leanh::LeanObject,
    mut v_k_1044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1045_: u8 = 0;
    let mut v_res_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1045_ = (crate::leanh::lean_unbox(v_t_1042_) as u8);
    v_res_1046_ = l_Lean_Compiler_InlineAttributeKind_ctorElim(
        v_motive_1040_,
        v_ctorIdx_1041_,
        v_t_boxed_1045_,
        v_h_1043_,
        v_k_1044_,
    );
    crate::leanh::lean_dec(v_k_1044_);
    crate::leanh::lean_dec(v_ctorIdx_1041_);
    return v_res_1046_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inline_elim___redArg(
    mut v_inline_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inline_1047_);
    return v_inline_1047_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inline_elim___redArg___boxed(
    mut v_inline_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1049_ = l_Lean_Compiler_InlineAttributeKind_inline_elim___redArg(v_inline_1048_);
    crate::leanh::lean_dec(v_inline_1048_);
    return v_res_1049_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inline_elim(
    mut v_motive_1050_: *mut crate::leanh::LeanObject,
    mut v_t_1051_: u8,
    mut v_h_1052_: *mut crate::leanh::LeanObject,
    mut v_inline_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inline_1053_);
    return v_inline_1053_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inline_elim___boxed(
    mut v_motive_1054_: *mut crate::leanh::LeanObject,
    mut v_t_1055_: *mut crate::leanh::LeanObject,
    mut v_h_1056_: *mut crate::leanh::LeanObject,
    mut v_inline_1057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1058_: u8 = 0;
    let mut v_res_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1058_ = (crate::leanh::lean_unbox(v_t_1055_) as u8);
    v_res_1059_ = l_Lean_Compiler_InlineAttributeKind_inline_elim(
        v_motive_1054_,
        v_t_boxed_1058_,
        v_h_1056_,
        v_inline_1057_,
    );
    crate::leanh::lean_dec(v_inline_1057_);
    return v_res_1059_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_noinline_elim___redArg(
    mut v_noinline_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_noinline_1060_);
    return v_noinline_1060_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_noinline_elim___redArg___boxed(
    mut v_noinline_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_Compiler_InlineAttributeKind_noinline_elim___redArg(v_noinline_1061_);
    crate::leanh::lean_dec(v_noinline_1061_);
    return v_res_1062_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_noinline_elim(
    mut v_motive_1063_: *mut crate::leanh::LeanObject,
    mut v_t_1064_: u8,
    mut v_h_1065_: *mut crate::leanh::LeanObject,
    mut v_noinline_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_noinline_1066_);
    return v_noinline_1066_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_noinline_elim___boxed(
    mut v_motive_1067_: *mut crate::leanh::LeanObject,
    mut v_t_1068_: *mut crate::leanh::LeanObject,
    mut v_h_1069_: *mut crate::leanh::LeanObject,
    mut v_noinline_1070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1071_: u8 = 0;
    let mut v_res_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1071_ = (crate::leanh::lean_unbox(v_t_1068_) as u8);
    v_res_1072_ = l_Lean_Compiler_InlineAttributeKind_noinline_elim(
        v_motive_1067_,
        v_t_boxed_1071_,
        v_h_1069_,
        v_noinline_1070_,
    );
    crate::leanh::lean_dec(v_noinline_1070_);
    return v_res_1072_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_macroInline_elim___redArg(
    mut v_macroInline_1073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_macroInline_1073_);
    return v_macroInline_1073_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_macroInline_elim___redArg___boxed(
    mut v_macroInline_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ =
        l_Lean_Compiler_InlineAttributeKind_macroInline_elim___redArg(v_macroInline_1074_);
    crate::leanh::lean_dec(v_macroInline_1074_);
    return v_res_1075_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_macroInline_elim(
    mut v_motive_1076_: *mut crate::leanh::LeanObject,
    mut v_t_1077_: u8,
    mut v_h_1078_: *mut crate::leanh::LeanObject,
    mut v_macroInline_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_macroInline_1079_);
    return v_macroInline_1079_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_macroInline_elim___boxed(
    mut v_motive_1080_: *mut crate::leanh::LeanObject,
    mut v_t_1081_: *mut crate::leanh::LeanObject,
    mut v_h_1082_: *mut crate::leanh::LeanObject,
    mut v_macroInline_1083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1084_: u8 = 0;
    let mut v_res_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1084_ = (crate::leanh::lean_unbox(v_t_1081_) as u8);
    v_res_1085_ = l_Lean_Compiler_InlineAttributeKind_macroInline_elim(
        v_motive_1080_,
        v_t_boxed_1084_,
        v_h_1082_,
        v_macroInline_1083_,
    );
    crate::leanh::lean_dec(v_macroInline_1083_);
    return v_res_1085_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inlineIfReduce_elim___redArg(
    mut v_inlineIfReduce_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inlineIfReduce_1086_);
    return v_inlineIfReduce_1086_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inlineIfReduce_elim___redArg___boxed(
    mut v_inlineIfReduce_1087_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1088_ =
        l_Lean_Compiler_InlineAttributeKind_inlineIfReduce_elim___redArg(v_inlineIfReduce_1087_);
    crate::leanh::lean_dec(v_inlineIfReduce_1087_);
    return v_res_1088_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inlineIfReduce_elim(
    mut v_motive_1089_: *mut crate::leanh::LeanObject,
    mut v_t_1090_: u8,
    mut v_h_1091_: *mut crate::leanh::LeanObject,
    mut v_inlineIfReduce_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inlineIfReduce_1092_);
    return v_inlineIfReduce_1092_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_inlineIfReduce_elim___boxed(
    mut v_motive_1093_: *mut crate::leanh::LeanObject,
    mut v_t_1094_: *mut crate::leanh::LeanObject,
    mut v_h_1095_: *mut crate::leanh::LeanObject,
    mut v_inlineIfReduce_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1097_: u8 = 0;
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1097_ = (crate::leanh::lean_unbox(v_t_1094_) as u8);
    v_res_1098_ = l_Lean_Compiler_InlineAttributeKind_inlineIfReduce_elim(
        v_motive_1093_,
        v_t_boxed_1097_,
        v_h_1095_,
        v_inlineIfReduce_1096_,
    );
    crate::leanh::lean_dec(v_inlineIfReduce_1096_);
    return v_res_1098_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_alwaysInline_elim___redArg(
    mut v_alwaysInline_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_alwaysInline_1099_);
    return v_alwaysInline_1099_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_alwaysInline_elim___redArg___boxed(
    mut v_alwaysInline_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ =
        l_Lean_Compiler_InlineAttributeKind_alwaysInline_elim___redArg(v_alwaysInline_1100_);
    crate::leanh::lean_dec(v_alwaysInline_1100_);
    return v_res_1101_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_alwaysInline_elim(
    mut v_motive_1102_: *mut crate::leanh::LeanObject,
    mut v_t_1103_: u8,
    mut v_h_1104_: *mut crate::leanh::LeanObject,
    mut v_alwaysInline_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_alwaysInline_1105_);
    return v_alwaysInline_1105_;
}
pub unsafe fn l_Lean_Compiler_InlineAttributeKind_alwaysInline_elim___boxed(
    mut v_motive_1106_: *mut crate::leanh::LeanObject,
    mut v_t_1107_: *mut crate::leanh::LeanObject,
    mut v_h_1108_: *mut crate::leanh::LeanObject,
    mut v_alwaysInline_1109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_t_boxed_1110_: u8 = 0;
    let mut v_res_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1110_ = (crate::leanh::lean_unbox(v_t_1107_) as u8);
    v_res_1111_ = l_Lean_Compiler_InlineAttributeKind_alwaysInline_elim(
        v_motive_1106_,
        v_t_boxed_1110_,
        v_h_1108_,
        v_alwaysInline_1109_,
    );
    crate::leanh::lean_dec(v_alwaysInline_1109_);
    return v_res_1111_;
}
pub unsafe fn _init_l_Lean_Compiler_instInhabitedInlineAttributeKind_default() -> u8 {
    let mut v___x_1112_: u8 = 0;
    v___x_1112_ = 0;
    return v___x_1112_;
}
pub unsafe fn _init_l_Lean_Compiler_instInhabitedInlineAttributeKind() -> u8 {
    let mut v___x_1113_: u8 = 0;
    v___x_1113_ = 0;
    return v___x_1113_;
}
pub unsafe fn l_Lean_Compiler_instBEqInlineAttributeKind_beq(
    mut v_x_1114_: u8,
    mut v_y_1115_: u8,
) -> u8 {
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: u8 = 0;
    v___x_1116_ = l_Lean_Compiler_InlineAttributeKind_ctorIdx(v_x_1114_);
    v___x_1117_ = l_Lean_Compiler_InlineAttributeKind_ctorIdx(v_y_1115_);
    v___x_1118_ = lean_nat_dec_eq(v___x_1116_, v___x_1117_);
    crate::leanh::lean_dec(v___x_1117_);
    crate::leanh::lean_dec(v___x_1116_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Compiler_instBEqInlineAttributeKind_beq___boxed(
    mut v_x_1119_: *mut crate::leanh::LeanObject,
    mut v_y_1120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_17__boxed_1121_: u8 = 0;
    let mut v_y_18__boxed_1122_: u8 = 0;
    let mut v_res_1123_: u8 = 0;
    let mut v_r_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_1121_ = (crate::leanh::lean_unbox(v_x_1119_) as u8);
    v_y_18__boxed_1122_ = (crate::leanh::lean_unbox(v_y_1120_) as u8);
    v_res_1123_ =
        l_Lean_Compiler_instBEqInlineAttributeKind_beq(v_x_17__boxed_1121_, v_y_18__boxed_1122_);
    v_r_1124_ = crate::leanh::lean_box((v_res_1123_) as usize);
    return v_r_1124_;
}
pub unsafe fn l_Lean_Compiler_instHashableInlineAttributeKind_hash(mut v_x_1127_: u8) -> u64 {
    match v_x_1127_ {
        0 => {
            let mut v___x_1128_: u64 = 0;
            v___x_1128_ = 0u64;
            return v___x_1128_;
        }
        1 => {
            let mut v___x_1129_: u64 = 0;
            v___x_1129_ = 1u64;
            return v___x_1129_;
        }
        2 => {
            let mut v___x_1130_: u64 = 0;
            v___x_1130_ = 2u64;
            return v___x_1130_;
        }
        3 => {
            let mut v___x_1131_: u64 = 0;
            v___x_1131_ = 3u64;
            return v___x_1131_;
        }
        _ => {
            let mut v___x_1132_: u64 = 0;
            v___x_1132_ = 4u64;
            return v___x_1132_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_instHashableInlineAttributeKind_hash___boxed(
    mut v_x_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_64__boxed_1134_: u8 = 0;
    let mut v_res_1135_: u64 = 0;
    let mut v_r_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_64__boxed_1134_ = (crate::leanh::lean_unbox(v_x_1133_) as u8);
    v_res_1135_ = l_Lean_Compiler_instHashableInlineAttributeKind_hash(v_x_64__boxed_1134_);
    v_r_1136_ = crate::leanh::lean_box_uint64(v_res_1135_);
    return v_r_1136_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString(
    mut v_x_1144_: u8,
) -> *mut crate::leanh::LeanObject {
    match v_x_1144_ {
        0 => {
            let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1145_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__0;
            return v___x_1145_;
        }
        1 => {
            let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1146_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__1;
            return v___x_1146_;
        }
        2 => {
            let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1147_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__2;
            return v___x_1147_;
        }
        3 => {
            let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1148_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__3;
            return v___x_1148_;
        }
        _ => {
            let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1149_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___closed__4;
            return v___x_1149_;
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString___boxed(
    mut v_x_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_49__boxed_1151_: u8 = 0;
    let mut v_res_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_49__boxed_1151_ = (crate::leanh::lean_unbox(v_x_1150_) as u8);
    v_res_1152_ =
        l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString(
            v_x_49__boxed_1151_,
        );
    return v_res_1152_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1153_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1154_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__0);
    v___x_1155_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1154_);
    return v___x_1155_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1156_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_1157_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1158_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1158_, 0, v___x_1157_);
    crate::leanh::lean_ctor_set(v___x_1158_, 1, v___x_1157_);
    crate::leanh::lean_ctor_set(v___x_1158_, 2, v___x_1157_);
    crate::leanh::lean_ctor_set(v___x_1158_, 3, v___x_1157_);
    crate::leanh::lean_ctor_set(v___x_1158_, 4, v___x_1156_);
    crate::leanh::lean_ctor_set(v___x_1158_, 5, v___x_1156_);
    crate::leanh::lean_ctor_set(v___x_1158_, 6, v___x_1156_);
    crate::leanh::lean_ctor_set(v___x_1158_, 7, v___x_1156_);
    crate::leanh::lean_ctor_set(v___x_1158_, 8, v___x_1156_);
    crate::leanh::lean_ctor_set(v___x_1158_, 9, v___x_1156_);
    return v___x_1158_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1159_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1160_ = lean_mk_empty_array_with_capacity(v___x_1159_);
    v___x_1161_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1161_, 0, v___x_1160_);
    return v___x_1161_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1162_: usize = 0;
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1162_ = 5usize;
    v___x_1163_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1164_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1165_ = lean_mk_empty_array_with_capacity(v___x_1164_);
    v___x_1166_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__3);
    v___x_1167_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1167_, 0, v___x_1166_);
    crate::leanh::lean_ctor_set(v___x_1167_, 1, v___x_1165_);
    crate::leanh::lean_ctor_set(v___x_1167_, 2, v___x_1163_);
    crate::leanh::lean_ctor_set(v___x_1167_, 3, v___x_1163_);
    crate::leanh::lean_ctor_set_usize(v___x_1167_, 4, v___x_1162_);
    return v___x_1167_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1168_ = crate::leanh::lean_box(1);
    v___x_1169_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__4);
    v___x_1170_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__1);
    v___x_1171_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1171_, 0, v___x_1170_);
    crate::leanh::lean_ctor_set(v___x_1171_, 1, v___x_1169_);
    crate::leanh::lean_ctor_set(v___x_1171_, 2, v___x_1168_);
    return v___x_1171_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1176_ = lean_st_ref_get(v___y_1174_);
    v_env_1177_ = crate::leanh::lean_ctor_get(v___x_1176_, 0);
    crate::leanh::lean_inc_ref(v_env_1177_);
    crate::leanh::lean_dec(v___x_1176_);
    v_options_1178_ = crate::leanh::lean_ctor_get(v___y_1173_, 2);
    v___x_1179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
    v___x_1180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5);
    crate::leanh::lean_inc_ref(v_options_1178_);
    v___x_1181_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1181_, 0, v_env_1177_);
    crate::leanh::lean_ctor_set(v___x_1181_, 1, v___x_1179_);
    crate::leanh::lean_ctor_set(v___x_1181_, 2, v___x_1180_);
    crate::leanh::lean_ctor_set(v___x_1181_, 3, v_options_1178_);
    v___x_1182_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1182_, 0, v___x_1181_);
    crate::leanh::lean_ctor_set(v___x_1182_, 1, v_msgData_1172_);
    v___x_1183_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1183_, 0, v___x_1182_);
    return v___x_1183_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1184_: *mut crate::leanh::LeanObject,
    mut v___y_1185_: *mut crate::leanh::LeanObject,
    mut v___y_1186_: *mut crate::leanh::LeanObject,
    mut v___y_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1188_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1184_, v___y_1185_, v___y_1186_);
    crate::leanh::lean_dec(v___y_1186_);
    crate::leanh::lean_dec_ref(v___y_1185_);
    return v_res_1188_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1189_: *mut crate::leanh::LeanObject,
    mut v___y_1190_: *mut crate::leanh::LeanObject,
    mut v___y_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1193_ = crate::leanh::lean_ctor_get(v___y_1190_, 5);
                v___x_1194_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1189_, v___y_1190_, v___y_1191_);
                v_a_1195_ = crate::leanh::lean_ctor_get(v___x_1194_, 0);
                v_isSharedCheck_1203_ = (!crate::leanh::lean_is_exclusive(v___x_1194_)) as u8;
                if v_isSharedCheck_1203_ == 0 {
                    v___x_1197_ = v___x_1194_;
                    v_isShared_1198_ = v_isSharedCheck_1203_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1195_);
                    crate::leanh::lean_dec(v___x_1194_);
                    v___x_1197_ = crate::leanh::lean_box(0);
                    v_isShared_1198_ = v_isSharedCheck_1203_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1193_);
                v___x_1199_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1199_, 0, v_ref_1193_);
                crate::leanh::lean_ctor_set(v___x_1199_, 1, v_a_1195_);
                if v_isShared_1198_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1197_, 1);
                    crate::leanh::lean_ctor_set(v___x_1197_, 0, v___x_1199_);
                    v___x_1201_ = v___x_1197_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
                    v___x_1201_ = v_reuseFailAlloc_1202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
    mut v___y_1207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1208_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1204_, v___y_1205_, v___y_1206_);
    crate::leanh::lean_dec(v___y_1206_);
    crate::leanh::lean_dec_ref(v___y_1205_);
    return v_res_1208_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1209_: *mut crate::leanh::LeanObject,
    mut v_msg_1210_: *mut crate::leanh::LeanObject,
    mut v___y_1211_: *mut crate::leanh::LeanObject,
    mut v___y_1212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1226_: u8 = 0;
    let mut v_cancelTk_x3f_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1228_: u8 = 0;
    let mut v_inheritedTraceOptions_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1214_ = crate::leanh::lean_ctor_get(v___y_1211_, 0);
    v_fileMap_1215_ = crate::leanh::lean_ctor_get(v___y_1211_, 1);
    v_options_1216_ = crate::leanh::lean_ctor_get(v___y_1211_, 2);
    v_currRecDepth_1217_ = crate::leanh::lean_ctor_get(v___y_1211_, 3);
    v_maxRecDepth_1218_ = crate::leanh::lean_ctor_get(v___y_1211_, 4);
    v_ref_1219_ = crate::leanh::lean_ctor_get(v___y_1211_, 5);
    v_currNamespace_1220_ = crate::leanh::lean_ctor_get(v___y_1211_, 6);
    v_openDecls_1221_ = crate::leanh::lean_ctor_get(v___y_1211_, 7);
    v_initHeartbeats_1222_ = crate::leanh::lean_ctor_get(v___y_1211_, 8);
    v_maxHeartbeats_1223_ = crate::leanh::lean_ctor_get(v___y_1211_, 9);
    v_quotContext_1224_ = crate::leanh::lean_ctor_get(v___y_1211_, 10);
    v_currMacroScope_1225_ = crate::leanh::lean_ctor_get(v___y_1211_, 11);
    v_diag_1226_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1211_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1227_ = crate::leanh::lean_ctor_get(v___y_1211_, 12);
    v_suppressElabErrors_1228_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1211_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1229_ = crate::leanh::lean_ctor_get(v___y_1211_, 13);
    v_ref_1230_ = l_Lean_replaceRef(v_ref_1209_, v_ref_1219_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1229_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1227_);
    crate::leanh::lean_inc(v_currMacroScope_1225_);
    crate::leanh::lean_inc(v_quotContext_1224_);
    crate::leanh::lean_inc(v_maxHeartbeats_1223_);
    crate::leanh::lean_inc(v_initHeartbeats_1222_);
    crate::leanh::lean_inc(v_openDecls_1221_);
    crate::leanh::lean_inc(v_currNamespace_1220_);
    crate::leanh::lean_inc(v_maxRecDepth_1218_);
    crate::leanh::lean_inc(v_currRecDepth_1217_);
    crate::leanh::lean_inc_ref(v_options_1216_);
    crate::leanh::lean_inc_ref(v_fileMap_1215_);
    crate::leanh::lean_inc_ref(v_fileName_1214_);
    v___x_1231_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1231_, 0, v_fileName_1214_);
    crate::leanh::lean_ctor_set(v___x_1231_, 1, v_fileMap_1215_);
    crate::leanh::lean_ctor_set(v___x_1231_, 2, v_options_1216_);
    crate::leanh::lean_ctor_set(v___x_1231_, 3, v_currRecDepth_1217_);
    crate::leanh::lean_ctor_set(v___x_1231_, 4, v_maxRecDepth_1218_);
    crate::leanh::lean_ctor_set(v___x_1231_, 5, v_ref_1230_);
    crate::leanh::lean_ctor_set(v___x_1231_, 6, v_currNamespace_1220_);
    crate::leanh::lean_ctor_set(v___x_1231_, 7, v_openDecls_1221_);
    crate::leanh::lean_ctor_set(v___x_1231_, 8, v_initHeartbeats_1222_);
    crate::leanh::lean_ctor_set(v___x_1231_, 9, v_maxHeartbeats_1223_);
    crate::leanh::lean_ctor_set(v___x_1231_, 10, v_quotContext_1224_);
    crate::leanh::lean_ctor_set(v___x_1231_, 11, v_currMacroScope_1225_);
    crate::leanh::lean_ctor_set(v___x_1231_, 12, v_cancelTk_x3f_1227_);
    crate::leanh::lean_ctor_set(v___x_1231_, 13, v_inheritedTraceOptions_1229_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1231_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1226_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1231_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1228_,
    );
    v___x_1232_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1210_, v___x_1231_, v___y_1212_);
    crate::leanh::lean_dec_ref_known(v___x_1231_, 14);
    return v___x_1232_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1233_: *mut crate::leanh::LeanObject,
    mut v_msg_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1238_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1233_, v_msg_1234_, v___y_1235_, v___y_1236_);
    crate::leanh::lean_dec(v___y_1236_);
    crate::leanh::lean_dec_ref(v___y_1235_);
    crate::leanh::lean_dec(v_ref_1233_);
    return v_res_1238_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1240_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0;
    v___x_1241_ = l_Lean_stringToMessageData(v___x_1240_);
    return v___x_1241_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1243_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2;
    v___x_1244_ = l_Lean_stringToMessageData(v___x_1243_);
    return v___x_1244_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1246_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4;
    v___x_1247_ = l_Lean_stringToMessageData(v___x_1246_);
    return v___x_1247_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1249_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1250_ = l_Lean_stringToMessageData(v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1252_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1253_ = l_Lean_stringToMessageData(v___x_1252_);
    return v___x_1253_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1255_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1256_ = l_Lean_stringToMessageData(v___x_1255_);
    return v___x_1256_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1258_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1259_ = l_Lean_stringToMessageData(v___x_1258_);
    return v___x_1259_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1260_: *mut crate::leanh::LeanObject,
    mut v_declHint_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: u8 = 0;
    let mut v_isExporting_1267_: u8 = 0;
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: u8 = 0;
    let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: u8 = 0;
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1321_: u8 = 0;
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1264_ = lean_st_ref_get(v___y_1262_);
                v_env_1265_ = crate::leanh::lean_ctor_get(v___x_1264_, 0);
                crate::leanh::lean_inc_ref(v_env_1265_);
                crate::leanh::lean_dec(v___x_1264_);
                v___x_1266_ = l_Lean_Name_isAnonymous(v_declHint_1261_);
                if v___x_1266_ == 0 {
                    v_isExporting_1267_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1265_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1267_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1265_);
                        crate::leanh::lean_dec(v_declHint_1261_);
                        v___x_1268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1268_, 0, v_msg_1260_);
                        return v___x_1268_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1265_);
                        v___x_1269_ = l_Lean_Environment_setExporting(v_env_1265_, v___x_1266_);
                        crate::leanh::lean_inc(v_declHint_1261_);
                        crate::leanh::lean_inc_ref(v___x_1269_);
                        v___x_1270_ = l_Lean_Environment_contains(
                            v___x_1269_,
                            v_declHint_1261_,
                            v_isExporting_1267_,
                        );
                        if v___x_1270_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1269_);
                            crate::leanh::lean_dec_ref(v_env_1265_);
                            crate::leanh::lean_dec(v_declHint_1261_);
                            v___x_1271_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1271_, 0, v_msg_1260_);
                            return v___x_1271_;
                        } else {
                            v___x_1272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__2);
                            v___x_1273_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___closed__5);
                            v___x_1274_ = l_Lean_Options_empty;
                            v___x_1275_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1269_);
                            crate::leanh::lean_ctor_set(v___x_1275_, 1, v___x_1272_);
                            crate::leanh::lean_ctor_set(v___x_1275_, 2, v___x_1273_);
                            crate::leanh::lean_ctor_set(v___x_1275_, 3, v___x_1274_);
                            crate::leanh::lean_inc(v_declHint_1261_);
                            v___x_1276_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1261_, v___x_1266_);
                            v_c_1277_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1277_, 0, v___x_1275_);
                            crate::leanh::lean_ctor_set(v_c_1277_, 1, v___x_1276_);
                            v___x_1278_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1265_,
                                v_declHint_1261_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1278_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1265_);
                                crate::leanh::lean_dec(v_declHint_1261_);
                                v___x_1279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                                v___x_1280_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1280_, 0, v___x_1279_);
                                crate::leanh::lean_ctor_set(v___x_1280_, 1, v_c_1277_);
                                v___x_1281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
                                v___x_1282_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1280_);
                                crate::leanh::lean_ctor_set(v___x_1282_, 1, v___x_1281_);
                                v___x_1283_ = l_Lean_MessageData_note(v___x_1282_);
                                v___x_1284_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1284_, 0, v_msg_1260_);
                                crate::leanh::lean_ctor_set(v___x_1284_, 1, v___x_1283_);
                                v___x_1285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1285_, 0, v___x_1284_);
                                return v___x_1285_;
                            } else {
                                v_val_1286_ = crate::leanh::lean_ctor_get(v___x_1278_, 0);
                                v_isSharedCheck_1321_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1278_)) as u8;
                                if v_isSharedCheck_1321_ == 0 {
                                    v___x_1288_ = v___x_1278_;
                                    v_isShared_1289_ = v_isSharedCheck_1321_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1286_);
                                    crate::leanh::lean_dec(v___x_1278_);
                                    v___x_1288_ = crate::leanh::lean_box(0);
                                    v_isShared_1289_ = v_isSharedCheck_1321_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1265_);
                    crate::leanh::lean_dec(v_declHint_1261_);
                    v___x_1322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1322_, 0, v_msg_1260_);
                    return v___x_1322_;
                }
            }
            1 => {
                v___x_1290_ = crate::leanh::lean_box(0);
                v___x_1291_ = l_Lean_Environment_header(v_env_1265_);
                crate::leanh::lean_dec_ref(v_env_1265_);
                v___x_1292_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1291_);
                v_mod_1293_ = lean_array_get(v___x_1290_, v___x_1292_, v_val_1286_);
                crate::leanh::lean_dec(v_val_1286_);
                crate::leanh::lean_dec_ref(v___x_1292_);
                v___x_1294_ = l_Lean_isPrivateName(v_declHint_1261_);
                crate::leanh::lean_dec(v_declHint_1261_);
                if v___x_1294_ == 0 {
                    v___x_1295_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                    v___x_1296_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1296_, 0, v___x_1295_);
                    crate::leanh::lean_ctor_set(v___x_1296_, 1, v_c_1277_);
                    v___x_1297_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1298_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1298_, 0, v___x_1296_);
                    crate::leanh::lean_ctor_set(v___x_1298_, 1, v___x_1297_);
                    v___x_1299_ = l_Lean_MessageData_ofName(v_mod_1293_);
                    v___x_1300_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1298_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 1, v___x_1299_);
                    v___x_1301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                    v___x_1302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1302_, 0, v___x_1300_);
                    crate::leanh::lean_ctor_set(v___x_1302_, 1, v___x_1301_);
                    v___x_1303_ = l_Lean_MessageData_note(v___x_1302_);
                    v___x_1304_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1304_, 0, v_msg_1260_);
                    crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1303_);
                    if v_isShared_1289_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1288_, 0);
                        crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1304_);
                        v___x_1306_ = v___x_1288_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
                        v___x_1306_ = v_reuseFailAlloc_1307_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1308_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_1309_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1309_, 0, v___x_1308_);
                    crate::leanh::lean_ctor_set(v___x_1309_, 1, v_c_1277_);
                    v___x_1310_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1311_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1311_, 0, v___x_1309_);
                    crate::leanh::lean_ctor_set(v___x_1311_, 1, v___x_1310_);
                    v___x_1312_ = l_Lean_MessageData_ofName(v_mod_1293_);
                    v___x_1313_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1313_, 0, v___x_1311_);
                    crate::leanh::lean_ctor_set(v___x_1313_, 1, v___x_1312_);
                    v___x_1314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1315_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1315_, 0, v___x_1313_);
                    crate::leanh::lean_ctor_set(v___x_1315_, 1, v___x_1314_);
                    v___x_1316_ = l_Lean_MessageData_note(v___x_1315_);
                    v___x_1317_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1317_, 0, v_msg_1260_);
                    crate::leanh::lean_ctor_set(v___x_1317_, 1, v___x_1316_);
                    if v_isShared_1289_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1288_, 0);
                        crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1317_);
                        v___x_1319_ = v___x_1288_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1320_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
                        v___x_1319_ = v_reuseFailAlloc_1320_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1306_;
            }
            3 => {
                return v___x_1319_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_1323_: *mut crate::leanh::LeanObject,
    mut v_declHint_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1323_, v_declHint_1324_, v___y_1325_);
    crate::leanh::lean_dec(v___y_1325_);
    return v_res_1327_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1328_: *mut crate::leanh::LeanObject,
    mut v_declHint_1329_: *mut crate::leanh::LeanObject,
    mut v___y_1330_: *mut crate::leanh::LeanObject,
    mut v___y_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1337_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1333_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1328_, v_declHint_1329_, v___y_1331_);
                v_a_1334_ = crate::leanh::lean_ctor_get(v___x_1333_, 0);
                v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v___x_1333_)) as u8;
                if v_isSharedCheck_1343_ == 0 {
                    v___x_1336_ = v___x_1333_;
                    v_isShared_1337_ = v_isSharedCheck_1343_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1334_);
                    crate::leanh::lean_dec(v___x_1333_);
                    v___x_1336_ = crate::leanh::lean_box(0);
                    v_isShared_1337_ = v_isSharedCheck_1343_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1338_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1339_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1339_, 0, v___x_1338_);
                crate::leanh::lean_ctor_set(v___x_1339_, 1, v_a_1334_);
                if v_isShared_1337_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1336_, 0, v___x_1339_);
                    v___x_1341_ = v___x_1336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1339_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1341_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_1344_: *mut crate::leanh::LeanObject,
    mut v_declHint_1345_: *mut crate::leanh::LeanObject,
    mut v___y_1346_: *mut crate::leanh::LeanObject,
    mut v___y_1347_: *mut crate::leanh::LeanObject,
    mut v___y_1348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1349_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1344_, v_declHint_1345_, v___y_1346_, v___y_1347_);
    crate::leanh::lean_dec(v___y_1347_);
    crate::leanh::lean_dec_ref(v___y_1346_);
    return v_res_1349_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1350_: *mut crate::leanh::LeanObject,
    mut v_msg_1351_: *mut crate::leanh::LeanObject,
    mut v_declHint_1352_: *mut crate::leanh::LeanObject,
    mut v___y_1353_: *mut crate::leanh::LeanObject,
    mut v___y_1354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1351_, v_declHint_1352_, v___y_1353_, v___y_1354_);
    v_a_1357_ = crate::leanh::lean_ctor_get(v___x_1356_, 0);
    crate::leanh::lean_inc(v_a_1357_);
    crate::leanh::lean_dec_ref(v___x_1356_);
    v___x_1358_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1350_, v_a_1357_, v___y_1353_, v___y_1354_);
    return v___x_1358_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1359_: *mut crate::leanh::LeanObject,
    mut v_msg_1360_: *mut crate::leanh::LeanObject,
    mut v_declHint_1361_: *mut crate::leanh::LeanObject,
    mut v___y_1362_: *mut crate::leanh::LeanObject,
    mut v___y_1363_: *mut crate::leanh::LeanObject,
    mut v___y_1364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1365_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1359_, v_msg_1360_, v_declHint_1361_, v___y_1362_, v___y_1363_);
    crate::leanh::lean_dec(v___y_1363_);
    crate::leanh::lean_dec_ref(v___y_1362_);
    crate::leanh::lean_dec(v_ref_1359_);
    return v_res_1365_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1368_ = l_Lean_stringToMessageData(v___x_1367_);
    return v___x_1368_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1371_ = l_Lean_stringToMessageData(v___x_1370_);
    return v___x_1371_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1372_: *mut crate::leanh::LeanObject,
    mut v_constName_1373_: *mut crate::leanh::LeanObject,
    mut v___y_1374_: *mut crate::leanh::LeanObject,
    mut v___y_1375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1377_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1378_ = 0;
    crate::leanh::lean_inc(v_constName_1373_);
    v___x_1379_ = l_Lean_MessageData_ofConstName(v_constName_1373_, v___x_1378_);
    v___x_1380_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1380_, 0, v___x_1377_);
    crate::leanh::lean_ctor_set(v___x_1380_, 1, v___x_1379_);
    v___x_1381_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1382_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1382_, 0, v___x_1380_);
    crate::leanh::lean_ctor_set(v___x_1382_, 1, v___x_1381_);
    v___x_1383_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1372_, v___x_1382_, v_constName_1373_, v___y_1374_, v___y_1375_);
    return v___x_1383_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1384_: *mut crate::leanh::LeanObject,
    mut v_constName_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v___y_1387_: *mut crate::leanh::LeanObject,
    mut v___y_1388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1389_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg(v_ref_1384_, v_constName_1385_, v___y_1386_, v___y_1387_);
    crate::leanh::lean_dec(v___y_1387_);
    crate::leanh::lean_dec_ref(v___y_1386_);
    crate::leanh::lean_dec(v_ref_1384_);
    return v_res_1389_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0___redArg(
    mut v_constName_1390_: *mut crate::leanh::LeanObject,
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v___y_1392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1394_ = crate::leanh::lean_ctor_get(v___y_1391_, 5);
    v___x_1395_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg(v_ref_1394_, v_constName_1390_, v___y_1391_, v___y_1392_);
    return v___x_1395_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0___redArg___boxed(
    mut v_constName_1396_: *mut crate::leanh::LeanObject,
    mut v___y_1397_: *mut crate::leanh::LeanObject,
    mut v___y_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1400_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0___redArg(v_constName_1396_, v___y_1397_, v___y_1398_);
    crate::leanh::lean_dec(v___y_1398_);
    crate::leanh::lean_dec_ref(v___y_1397_);
    return v_res_1400_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(
    mut v_constName_1401_: *mut crate::leanh::LeanObject,
    mut v___y_1402_: *mut crate::leanh::LeanObject,
    mut v___y_1403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: u8 = 0;
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1413_: u8 = 0;
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1417_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1405_ = lean_st_ref_get(v___y_1403_);
                v_env_1406_ = crate::leanh::lean_ctor_get(v___x_1405_, 0);
                crate::leanh::lean_inc_ref(v_env_1406_);
                crate::leanh::lean_dec(v___x_1405_);
                v___x_1407_ = 0;
                crate::leanh::lean_inc(v_constName_1401_);
                v___x_1408_ =
                    l_Lean_Environment_find_x3f(v_env_1406_, v_constName_1401_, v___x_1407_);
                if crate::leanh::lean_obj_tag(v___x_1408_) == 0 {
                    v___x_1409_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0___redArg(v_constName_1401_, v___y_1402_, v___y_1403_);
                    return v___x_1409_;
                } else {
                    crate::leanh::lean_dec(v_constName_1401_);
                    v_val_1410_ = crate::leanh::lean_ctor_get(v___x_1408_, 0);
                    v_isSharedCheck_1417_ = (!crate::leanh::lean_is_exclusive(v___x_1408_)) as u8;
                    if v_isSharedCheck_1417_ == 0 {
                        v___x_1412_ = v___x_1408_;
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1410_);
                        crate::leanh::lean_dec(v___x_1408_);
                        v___x_1412_ = crate::leanh::lean_box(0);
                        v_isShared_1413_ = v_isSharedCheck_1417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1413_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1412_, 0);
                    v___x_1415_ = v___x_1412_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1416_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_val_1410_);
                    v___x_1415_ = v_reuseFailAlloc_1416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1415_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0___boxed(
    mut v_constName_1418_: *mut crate::leanh::LeanObject,
    mut v___y_1419_: *mut crate::leanh::LeanObject,
    mut v___y_1420_: *mut crate::leanh::LeanObject,
    mut v___y_1421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1422_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(v_constName_1418_, v___y_1419_, v___y_1420_);
    crate::leanh::lean_dec(v___y_1420_);
    crate::leanh::lean_dec_ref(v___y_1419_);
    return v_res_1422_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(
    mut v_declName_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1431_: u8 = 0;
    let mut v_val_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1445_: u8 = 0;
    let mut v___x_1446_: u8 = 0;
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1451_: u8 = 0;
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1456_: u8 = 0;
    let mut v___x_1457_: u8 = 0;
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v_a_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1466_: u8 = 0;
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1470_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_1423_);
                v___x_1427_ = l_Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(v_declName_1423_, v_a_1424_, v_a_1425_);
                if crate::leanh::lean_obj_tag(v___x_1427_) == 0 {
                    v_a_1428_ = crate::leanh::lean_ctor_get(v___x_1427_, 0);
                    v_isSharedCheck_1462_ = (!crate::leanh::lean_is_exclusive(v___x_1427_)) as u8;
                    if v_isSharedCheck_1462_ == 0 {
                        v___x_1430_ = v___x_1427_;
                        v_isShared_1431_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1428_);
                        crate::leanh::lean_dec(v___x_1427_);
                        v___x_1430_ = crate::leanh::lean_box(0);
                        v_isShared_1431_ = v_isSharedCheck_1462_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_1423_);
                    v_a_1463_ = crate::leanh::lean_ctor_get(v___x_1427_, 0);
                    v_isSharedCheck_1470_ = (!crate::leanh::lean_is_exclusive(v___x_1427_)) as u8;
                    if v_isSharedCheck_1470_ == 0 {
                        v___x_1465_ = v___x_1427_;
                        v_isShared_1466_ = v_isSharedCheck_1470_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1463_);
                        crate::leanh::lean_dec(v___x_1427_);
                        v___x_1465_ = crate::leanh::lean_box(0);
                        v_isShared_1466_ = v_isSharedCheck_1470_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1428_) == 1 {
                    v_val_1432_ = crate::leanh::lean_ctor_get(v_a_1428_, 0);
                    crate::leanh::lean_inc_ref(v_val_1432_);
                    crate::leanh::lean_dec_ref_known(v_a_1428_, 1);
                    v_all_1433_ = crate::leanh::lean_ctor_get(v_val_1432_, 3);
                    crate::leanh::lean_inc(v_all_1433_);
                    crate::leanh::lean_dec_ref(v_val_1432_);
                    v___x_1434_ = l_List_lengthTR___redArg(v_all_1433_);
                    crate::leanh::lean_dec(v_all_1433_);
                    v___x_1435_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1436_ = lean_nat_dec_eq(v___x_1434_, v___x_1435_);
                    crate::leanh::lean_dec(v___x_1434_);
                    if v___x_1436_ == 0 {
                        crate::leanh::lean_dec(v_declName_1423_);
                        v___x_1437_ = crate::leanh::lean_box((v___x_1436_) as usize);
                        if v_isShared_1431_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1430_, 0, v___x_1437_);
                            v___x_1439_ = v___x_1430_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1440_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
                            v___x_1439_ = v_reuseFailAlloc_1440_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1430_);
                        v___x_1441_ =
                            l_Lean_Meta_isRecursiveDefinition___redArg(v_declName_1423_, v_a_1425_);
                        if crate::leanh::lean_obj_tag(v___x_1441_) == 0 {
                            v_a_1442_ = crate::leanh::lean_ctor_get(v___x_1441_, 0);
                            v_isSharedCheck_1456_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1441_)) as u8;
                            if v_isSharedCheck_1456_ == 0 {
                                v___x_1444_ = v___x_1441_;
                                v_isShared_1445_ = v_isSharedCheck_1456_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1442_);
                                crate::leanh::lean_dec(v___x_1441_);
                                v___x_1444_ = crate::leanh::lean_box(0);
                                v_isShared_1445_ = v_isSharedCheck_1456_;
                                state = 3;
                                continue;
                            }
                        } else {
                            return v___x_1441_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1428_);
                    crate::leanh::lean_dec(v_declName_1423_);
                    v___x_1457_ = 0;
                    v___x_1458_ = crate::leanh::lean_box((v___x_1457_) as usize);
                    if v_isShared_1431_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1430_, 0, v___x_1458_);
                        v___x_1460_ = v___x_1430_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
                        v___x_1460_ = v_reuseFailAlloc_1461_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1439_;
            }
            3 => {
                v___x_1446_ = (crate::leanh::lean_unbox(v_a_1442_) as u8);
                crate::leanh::lean_dec(v_a_1442_);
                if v___x_1446_ == 0 {
                    v___x_1447_ = crate::leanh::lean_box((v___x_1436_) as usize);
                    if v_isShared_1445_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1447_);
                        v___x_1449_ = v___x_1444_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1450_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1447_);
                        v___x_1449_ = v_reuseFailAlloc_1450_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_1451_ = 0;
                    v___x_1452_ = crate::leanh::lean_box((v___x_1451_) as usize);
                    if v_isShared_1445_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1452_);
                        v___x_1454_ = v___x_1444_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1452_);
                        v___x_1454_ = v_reuseFailAlloc_1455_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_1449_;
            }
            5 => {
                return v___x_1454_;
            }
            6 => {
                return v___x_1460_;
            }
            7 => {
                if v_isShared_1466_ == 0 {
                    v___x_1468_ = v___x_1465_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
                    v___x_1468_ = v_reuseFailAlloc_1469_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1468_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline___boxed(
    mut v_declName_1471_: *mut crate::leanh::LeanObject,
    mut v_a_1472_: *mut crate::leanh::LeanObject,
    mut v_a_1473_: *mut crate::leanh::LeanObject,
    mut v_a_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1475_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(
        v_declName_1471_,
        v_a_1472_,
        v_a_1473_,
    );
    crate::leanh::lean_dec(v_a_1473_);
    crate::leanh::lean_dec_ref(v_a_1472_);
    return v_res_1475_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0(
    mut v_00_u03b1_1476_: *mut crate::leanh::LeanObject,
    mut v_constName_1477_: *mut crate::leanh::LeanObject,
    mut v___y_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1481_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0___redArg(v_constName_1477_, v___y_1478_, v___y_1479_);
    return v___x_1481_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0___boxed(
    mut v_00_u03b1_1482_: *mut crate::leanh::LeanObject,
    mut v_constName_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
    mut v___y_1485_: *mut crate::leanh::LeanObject,
    mut v___y_1486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1487_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0(v_00_u03b1_1482_, v_constName_1483_, v___y_1484_, v___y_1485_);
    crate::leanh::lean_dec(v___y_1485_);
    crate::leanh::lean_dec_ref(v___y_1484_);
    return v_res_1487_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1488_: *mut crate::leanh::LeanObject,
    mut v_ref_1489_: *mut crate::leanh::LeanObject,
    mut v_constName_1490_: *mut crate::leanh::LeanObject,
    mut v___y_1491_: *mut crate::leanh::LeanObject,
    mut v___y_1492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1494_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___redArg(v_ref_1489_, v_constName_1490_, v___y_1491_, v___y_1492_);
    return v___x_1494_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1495_: *mut crate::leanh::LeanObject,
    mut v_ref_1496_: *mut crate::leanh::LeanObject,
    mut v_constName_1497_: *mut crate::leanh::LeanObject,
    mut v___y_1498_: *mut crate::leanh::LeanObject,
    mut v___y_1499_: *mut crate::leanh::LeanObject,
    mut v___y_1500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1501_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1(v_00_u03b1_1495_, v_ref_1496_, v_constName_1497_, v___y_1498_, v___y_1499_);
    crate::leanh::lean_dec(v___y_1499_);
    crate::leanh::lean_dec_ref(v___y_1498_);
    crate::leanh::lean_dec(v_ref_1496_);
    return v_res_1501_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_1502_: *mut crate::leanh::LeanObject,
    mut v_ref_1503_: *mut crate::leanh::LeanObject,
    mut v_msg_1504_: *mut crate::leanh::LeanObject,
    mut v_declHint_1505_: *mut crate::leanh::LeanObject,
    mut v___y_1506_: *mut crate::leanh::LeanObject,
    mut v___y_1507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1503_, v_msg_1504_, v_declHint_1505_, v___y_1506_, v___y_1507_);
    return v___x_1509_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_1510_: *mut crate::leanh::LeanObject,
    mut v_ref_1511_: *mut crate::leanh::LeanObject,
    mut v_msg_1512_: *mut crate::leanh::LeanObject,
    mut v_declHint_1513_: *mut crate::leanh::LeanObject,
    mut v___y_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1510_, v_ref_1511_, v_msg_1512_, v_declHint_1513_, v___y_1514_, v___y_1515_);
    crate::leanh::lean_dec(v___y_1515_);
    crate::leanh::lean_dec_ref(v___y_1514_);
    crate::leanh::lean_dec(v_ref_1511_);
    return v_res_1517_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_1518_: *mut crate::leanh::LeanObject,
    mut v_declHint_1519_: *mut crate::leanh::LeanObject,
    mut v___y_1520_: *mut crate::leanh::LeanObject,
    mut v___y_1521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1523_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1518_, v_declHint_1519_, v___y_1521_);
    return v___x_1523_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1524_: *mut crate::leanh::LeanObject,
    mut v_declHint_1525_: *mut crate::leanh::LeanObject,
    mut v___y_1526_: *mut crate::leanh::LeanObject,
    mut v___y_1527_: *mut crate::leanh::LeanObject,
    mut v___y_1528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1529_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1524_, v_declHint_1525_, v___y_1526_, v___y_1527_);
    crate::leanh::lean_dec(v___y_1527_);
    crate::leanh::lean_dec_ref(v___y_1526_);
    return v_res_1529_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_1530_: *mut crate::leanh::LeanObject,
    mut v_ref_1531_: *mut crate::leanh::LeanObject,
    mut v_msg_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1536_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1531_, v_msg_1532_, v___y_1533_, v___y_1534_);
    return v___x_1536_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_1537_: *mut crate::leanh::LeanObject,
    mut v_ref_1538_: *mut crate::leanh::LeanObject,
    mut v_msg_1539_: *mut crate::leanh::LeanObject,
    mut v___y_1540_: *mut crate::leanh::LeanObject,
    mut v___y_1541_: *mut crate::leanh::LeanObject,
    mut v___y_1542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1543_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_1537_, v_ref_1538_, v_msg_1539_, v___y_1540_, v___y_1541_);
    crate::leanh::lean_dec(v___y_1541_);
    crate::leanh::lean_dec_ref(v___y_1540_);
    crate::leanh::lean_dec(v_ref_1538_);
    return v_res_1543_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_1544_: *mut crate::leanh::LeanObject,
    mut v_msg_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1545_, v___y_1546_, v___y_1547_);
    return v___x_1549_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_1550_: *mut crate::leanh::LeanObject,
    mut v_msg_1551_: *mut crate::leanh::LeanObject,
    mut v___y_1552_: *mut crate::leanh::LeanObject,
    mut v___y_1553_: *mut crate::leanh::LeanObject,
    mut v___y_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1555_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_1550_, v_msg_1551_, v___y_1552_, v___y_1553_);
    crate::leanh::lean_dec(v___y_1553_);
    crate::leanh::lean_dec_ref(v___y_1552_);
    return v_res_1555_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_(
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1559_ = lean_st_ref_get(v___y_1557_);
    v_env_1560_ = crate::leanh::lean_ctor_get(v___x_1559_, 0);
    crate::leanh::lean_inc_ref(v_env_1560_);
    crate::leanh::lean_dec(v___x_1559_);
    v___x_1561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1561_, 0, v_env_1560_);
    return v___x_1561_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2____boxed(
    mut v___y_1562_: *mut crate::leanh::LeanObject,
    mut v___y_1563_: *mut crate::leanh::LeanObject,
    mut v___y_1564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1565_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_(v___y_1562_, v___y_1563_);
    crate::leanh::lean_dec(v___y_1563_);
    crate::leanh::lean_dec_ref(v___y_1562_);
    return v_res_1565_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(
    mut v___y_1566_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1567_: u8,
    mut v___x_1568_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1582_: u8 = 0;
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut v_unused_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1571_ = lean_st_ref_take(v___y_1566_);
                v_env_1572_ = crate::leanh::lean_ctor_get(v___x_1571_, 0);
                v_nextMacroScope_1573_ = crate::leanh::lean_ctor_get(v___x_1571_, 1);
                v_ngen_1574_ = crate::leanh::lean_ctor_get(v___x_1571_, 2);
                v_auxDeclNGen_1575_ = crate::leanh::lean_ctor_get(v___x_1571_, 3);
                v_traceState_1576_ = crate::leanh::lean_ctor_get(v___x_1571_, 4);
                v_messages_1577_ = crate::leanh::lean_ctor_get(v___x_1571_, 6);
                v_infoState_1578_ = crate::leanh::lean_ctor_get(v___x_1571_, 7);
                v_snapshotTasks_1579_ = crate::leanh::lean_ctor_get(v___x_1571_, 8);
                v_isSharedCheck_1590_ = (!crate::leanh::lean_is_exclusive(v___x_1571_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v_unused_1591_ = crate::leanh::lean_ctor_get(v___x_1571_, 5);
                    crate::leanh::lean_dec(v_unused_1591_);
                    v___x_1581_ = v___x_1571_;
                    v_isShared_1582_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1579_);
                    crate::leanh::lean_inc(v_infoState_1578_);
                    crate::leanh::lean_inc(v_messages_1577_);
                    crate::leanh::lean_inc(v_traceState_1576_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1575_);
                    crate::leanh::lean_inc(v_ngen_1574_);
                    crate::leanh::lean_inc(v_nextMacroScope_1573_);
                    crate::leanh::lean_inc(v_env_1572_);
                    crate::leanh::lean_dec(v___x_1571_);
                    v___x_1581_ = crate::leanh::lean_box(0);
                    v_isShared_1582_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1583_ = l_Lean_Environment_setExporting(v_env_1572_, v_isExporting_1567_);
                if v_isShared_1582_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1581_, 5, v___x_1568_);
                    crate::leanh::lean_ctor_set(v___x_1581_, 0, v___x_1583_);
                    v___x_1585_ = v___x_1581_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1583_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_nextMacroScope_1573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 2, v_ngen_1574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 3, v_auxDeclNGen_1575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 4, v_traceState_1576_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 5, v___x_1568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 6, v_messages_1577_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 7, v_infoState_1578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 8, v_snapshotTasks_1579_);
                    v___x_1585_ = v_reuseFailAlloc_1589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1586_ = lean_st_ref_set(v___y_1566_, v___x_1585_);
                v___x_1587_ = crate::leanh::lean_box(0);
                v___x_1588_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1588_, 0, v___x_1587_);
                return v___x_1588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0___boxed(
    mut v___y_1592_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1593_: *mut crate::leanh::LeanObject,
    mut v___x_1594_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_1597_: u8 = 0;
    let mut v_res_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1597_ = (crate::leanh::lean_unbox(v_isExporting_1593_) as u8);
    v_res_1598_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(v___y_1592_, v_isExporting_boxed_1597_, v___x_1594_, v_a_x3f_1595_);
    crate::leanh::lean_dec(v_a_x3f_1595_);
    crate::leanh::lean_dec(v___y_1592_);
    return v_res_1598_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1599_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1600_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
    v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1601_, 0, v___x_1600_);
    return v___x_1601_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__1);
    v___x_1603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1603_, 0, v___x_1602_);
    crate::leanh::lean_ctor_set(v___x_1603_, 1, v___x_1602_);
    return v___x_1603_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1605_: u8,
    mut v___y_1606_: *mut crate::leanh::LeanObject,
    mut v___y_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1611_: u8 = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1633_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1639_: u8 = 0;
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1643_: u8 = 0;
    let mut v_unused_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1646_: u8 = 0;
    let mut v_a_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1656_: u8 = 0;
    let mut v_unused_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1659_: u8 = 0;
    let mut v_unused_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = lean_st_ref_get(v___y_1607_);
                v_env_1610_ = crate::leanh::lean_ctor_get(v___x_1609_, 0);
                crate::leanh::lean_inc_ref(v_env_1610_);
                crate::leanh::lean_dec(v___x_1609_);
                v_isExporting_1611_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1610_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_1610_);
                v___x_1612_ = lean_st_ref_take(v___y_1607_);
                v_env_1613_ = crate::leanh::lean_ctor_get(v___x_1612_, 0);
                v_nextMacroScope_1614_ = crate::leanh::lean_ctor_get(v___x_1612_, 1);
                v_ngen_1615_ = crate::leanh::lean_ctor_get(v___x_1612_, 2);
                v_auxDeclNGen_1616_ = crate::leanh::lean_ctor_get(v___x_1612_, 3);
                v_traceState_1617_ = crate::leanh::lean_ctor_get(v___x_1612_, 4);
                v_messages_1618_ = crate::leanh::lean_ctor_get(v___x_1612_, 6);
                v_infoState_1619_ = crate::leanh::lean_ctor_get(v___x_1612_, 7);
                v_snapshotTasks_1620_ = crate::leanh::lean_ctor_get(v___x_1612_, 8);
                v_isSharedCheck_1659_ = (!crate::leanh::lean_is_exclusive(v___x_1612_)) as u8;
                if v_isSharedCheck_1659_ == 0 {
                    v_unused_1660_ = crate::leanh::lean_ctor_get(v___x_1612_, 5);
                    crate::leanh::lean_dec(v_unused_1660_);
                    v___x_1622_ = v___x_1612_;
                    v_isShared_1623_ = v_isSharedCheck_1659_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1620_);
                    crate::leanh::lean_inc(v_infoState_1619_);
                    crate::leanh::lean_inc(v_messages_1618_);
                    crate::leanh::lean_inc(v_traceState_1617_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1616_);
                    crate::leanh::lean_inc(v_ngen_1615_);
                    crate::leanh::lean_inc(v_nextMacroScope_1614_);
                    crate::leanh::lean_inc(v_env_1613_);
                    crate::leanh::lean_dec(v___x_1612_);
                    v___x_1622_ = crate::leanh::lean_box(0);
                    v_isShared_1623_ = v_isSharedCheck_1659_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1624_ = l_Lean_Environment_setExporting(v_env_1613_, v_isExporting_1605_);
                v___x_1625_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__2);
                if v_isShared_1623_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1622_, 5, v___x_1625_);
                    crate::leanh::lean_ctor_set(v___x_1622_, 0, v___x_1624_);
                    v___x_1627_ = v___x_1622_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1624_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_nextMacroScope_1614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_ngen_1615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 3, v_auxDeclNGen_1616_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 4, v_traceState_1617_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 5, v___x_1625_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 6, v_messages_1618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 7, v_infoState_1619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 8, v_snapshotTasks_1620_);
                    v___x_1627_ = v_reuseFailAlloc_1658_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1628_ = lean_st_ref_set(v___y_1607_, v___x_1627_);
                crate::leanh::lean_inc(v___y_1607_);
                crate::leanh::lean_inc_ref(v___y_1606_);
                v_r_1629_ = crate::leanh::lean_apply_3(
                    v_x_1604_,
                    v___y_1606_,
                    v___y_1607_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_1629_) == 0 {
                    v_a_1630_ = crate::leanh::lean_ctor_get(v_r_1629_, 0);
                    v_isSharedCheck_1646_ = (!crate::leanh::lean_is_exclusive(v_r_1629_)) as u8;
                    if v_isSharedCheck_1646_ == 0 {
                        v___x_1632_ = v_r_1629_;
                        v_isShared_1633_ = v_isSharedCheck_1646_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1630_);
                        crate::leanh::lean_dec(v_r_1629_);
                        v___x_1632_ = crate::leanh::lean_box(0);
                        v_isShared_1633_ = v_isSharedCheck_1646_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1647_ = crate::leanh::lean_ctor_get(v_r_1629_, 0);
                    crate::leanh::lean_inc(v_a_1647_);
                    crate::leanh::lean_dec_ref_known(v_r_1629_, 1);
                    v___x_1648_ = crate::leanh::lean_box(0);
                    v___x_1649_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(v___y_1607_, v_isExporting_1611_, v___x_1625_, v___x_1648_);
                    v_isSharedCheck_1656_ = (!crate::leanh::lean_is_exclusive(v___x_1649_)) as u8;
                    if v_isSharedCheck_1656_ == 0 {
                        v_unused_1657_ = crate::leanh::lean_ctor_get(v___x_1649_, 0);
                        crate::leanh::lean_dec(v_unused_1657_);
                        v___x_1651_ = v___x_1649_;
                        v_isShared_1652_ = v_isSharedCheck_1656_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1649_);
                        v___x_1651_ = crate::leanh::lean_box(0);
                        v_isShared_1652_ = v_isSharedCheck_1656_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_1630_);
                if v_isShared_1633_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1632_, 1);
                    v___x_1635_ = v___x_1632_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1630_);
                    v___x_1635_ = v_reuseFailAlloc_1645_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1636_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___lam__0(v___y_1607_, v_isExporting_1611_, v___x_1625_, v___x_1635_);
                crate::leanh::lean_dec_ref(v___x_1635_);
                v_isSharedCheck_1643_ = (!crate::leanh::lean_is_exclusive(v___x_1636_)) as u8;
                if v_isSharedCheck_1643_ == 0 {
                    v_unused_1644_ = crate::leanh::lean_ctor_get(v___x_1636_, 0);
                    crate::leanh::lean_dec(v_unused_1644_);
                    v___x_1638_ = v___x_1636_;
                    v_isShared_1639_ = v_isSharedCheck_1643_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1636_);
                    v___x_1638_ = crate::leanh::lean_box(0);
                    v_isShared_1639_ = v_isSharedCheck_1643_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1638_, 0, v_a_1630_);
                    v___x_1641_ = v___x_1638_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1642_, 0, v_a_1630_);
                    v___x_1641_ = v_reuseFailAlloc_1642_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1641_;
            }
            7 => {
                if v_isShared_1652_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1651_, 1);
                    crate::leanh::lean_ctor_set(v___x_1651_, 0, v_a_1647_);
                    v___x_1654_ = v___x_1651_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1655_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_a_1647_);
                    v___x_1654_ = v_reuseFailAlloc_1655_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1654_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_x_1661_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_1666_: u8 = 0;
    let mut v_res_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1666_ = (crate::leanh::lean_unbox(v_isExporting_1662_) as u8);
    v_res_1667_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1661_, v_isExporting_boxed_1666_, v___y_1663_, v___y_1664_);
    crate::leanh::lean_dec(v___y_1664_);
    crate::leanh::lean_dec_ref(v___y_1663_);
    return v_res_1667_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0___redArg(
    mut v_x_1668_: *mut crate::leanh::LeanObject,
    mut v_when_1669_: u8,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_1669_ == 0 {
        let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_1671_);
        crate::leanh::lean_inc_ref(v___y_1670_);
        v___x_1673_ = crate::leanh::lean_apply_3(
            v_x_1668_,
            v___y_1670_,
            v___y_1671_,
            crate::leanh::lean_box(0),
        );
        return v___x_1673_;
    } else {
        let mut v___x_1674_: u8 = 0;
        let mut v___x_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1674_ = 0;
        v___x_1675_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1668_, v___x_1674_, v___y_1670_, v___y_1671_);
        return v___x_1675_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_x_1676_: *mut crate::leanh::LeanObject,
    mut v_when_1677_: *mut crate::leanh::LeanObject,
    mut v___y_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_1681_: u8 = 0;
    let mut v_res_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_1681_ = (crate::leanh::lean_unbox(v_when_1677_) as u8);
    v_res_1682_ = l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0___redArg(v_x_1676_, v_when_boxed_1681_, v___y_1678_, v___y_1679_);
    crate::leanh::lean_dec(v___y_1679_);
    crate::leanh::lean_dec_ref(v___y_1678_);
    return v_res_1682_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___redArg(
    mut v_x_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1693_: u8 = 0;
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1683_) == 0 {
                    v_a_1687_ = crate::leanh::lean_ctor_get(v_x_1683_, 0);
                    crate::leanh::lean_inc(v_a_1687_);
                    crate::leanh::lean_dec_ref_known(v_x_1683_, 1);
                    v___x_1688_ = l_Lean_stringToMessageData(v_a_1687_);
                    v___x_1689_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v___x_1688_, v___y_1684_, v___y_1685_);
                    return v___x_1689_;
                } else {
                    v_a_1690_ = crate::leanh::lean_ctor_get(v_x_1683_, 0);
                    v_isSharedCheck_1697_ = (!crate::leanh::lean_is_exclusive(v_x_1683_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1692_ = v_x_1683_;
                        v_isShared_1693_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1690_);
                        crate::leanh::lean_dec(v_x_1683_);
                        v___x_1692_ = crate::leanh::lean_box(0);
                        v_isShared_1693_ = v_isSharedCheck_1697_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1693_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1692_, 0);
                    v___x_1695_ = v___x_1692_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
                    v___x_1695_ = v_reuseFailAlloc_1696_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_x_1698_: *mut crate::leanh::LeanObject,
    mut v___y_1699_: *mut crate::leanh::LeanObject,
    mut v___y_1700_: *mut crate::leanh::LeanObject,
    mut v___y_1701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1702_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___redArg(v_x_1698_, v___y_1699_, v___y_1700_);
    crate::leanh::lean_dec(v___y_1700_);
    crate::leanh::lean_dec_ref(v___y_1699_);
    return v_res_1702_;
}
pub unsafe fn _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1704_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__0_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1705_ = l_Lean_stringToMessageData(v___x_1704_);
    return v___x_1705_;
}
pub unsafe fn _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1707_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__2_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1708_ = l_Lean_stringToMessageData(v___x_1707_);
    return v___x_1708_;
}
pub unsafe fn _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1710_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__4_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1711_ = l_Lean_stringToMessageData(v___x_1710_);
    return v___x_1711_;
}
pub unsafe fn _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1713_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__6_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1714_ = l_Lean_stringToMessageData(v___x_1713_);
    return v___x_1714_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_(
    mut v___f_1717_: *mut crate::leanh::LeanObject,
    mut v_declName_1718_: *mut crate::leanh::LeanObject,
    mut v_kind_1719_: u8,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
    mut v___y_1721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1730_: u8 = 0;
    let mut v___x_1731_: u8 = 0;
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: u8 = 0;
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut v_a_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1747_: u8 = 0;
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: u8 = 0;
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1769_: u8 = 0;
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1785_: u8 = 0;
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1789_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_kind_1719_ == 2 {
                    crate::leanh::lean_dec_ref(v___f_1717_);
                    v___x_1752_ = lean_st_ref_get(v___y_1721_);
                    v_env_1753_ = crate::leanh::lean_ctor_get(v___x_1752_, 0);
                    crate::leanh::lean_inc_ref(v_env_1753_);
                    crate::leanh::lean_dec(v___x_1752_);
                    crate::leanh::lean_inc(v_declName_1718_);
                    v___x_1754_ = l_Lean_Compiler_checkIsDefinition(v_env_1753_, v_declName_1718_);
                    if crate::leanh::lean_obj_tag(v___x_1754_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1754_, 1);
                        v___x_1755_ = 0;
                        v___x_1756_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__5_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_);
                        v___x_1757_ = l_Lean_MessageData_ofConstName(v_declName_1718_, v___x_1755_);
                        v___x_1758_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1758_, 0, v___x_1756_);
                        crate::leanh::lean_ctor_set(v___x_1758_, 1, v___x_1757_);
                        v___x_1759_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__7_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_);
                        v___x_1760_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1760_, 0, v___x_1758_);
                        crate::leanh::lean_ctor_set(v___x_1760_, 1, v___x_1759_);
                        v___x_1761_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v___x_1760_, v___y_1720_, v___y_1721_);
                        return v___x_1761_;
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1754_, 1);
                        v___y_1724_ = v___y_1720_;
                        v___y_1725_ = v___y_1721_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1762_ = 1;
                    v___x_1763_ = l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0___redArg(v___f_1717_, v___x_1762_, v___y_1720_, v___y_1721_);
                    if crate::leanh::lean_obj_tag(v___x_1763_) == 0 {
                        v_a_1764_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                        crate::leanh::lean_inc(v_a_1764_);
                        crate::leanh::lean_dec_ref_known(v___x_1763_, 1);
                        v___x_1765_ =
                            l_Lean_Compiler_checkIsDefinition(v_a_1764_, v_declName_1718_);
                        if crate::leanh::lean_obj_tag(v___x_1765_) == 0 {
                            v_a_1766_ = crate::leanh::lean_ctor_get(v___x_1765_, 0);
                            v_isSharedCheck_1780_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1765_)) as u8;
                            if v_isSharedCheck_1780_ == 0 {
                                v___x_1768_ = v___x_1765_;
                                v_isShared_1769_ = v_isSharedCheck_1780_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1766_);
                                crate::leanh::lean_dec(v___x_1765_);
                                v___x_1768_ = crate::leanh::lean_box(0);
                                v_isShared_1769_ = v_isSharedCheck_1780_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v___x_1781_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___redArg(v___x_1765_, v___y_1720_, v___y_1721_);
                            return v___x_1781_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_1718_);
                        v_a_1782_ = crate::leanh::lean_ctor_get(v___x_1763_, 0);
                        v_isSharedCheck_1789_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1763_)) as u8;
                        if v_isSharedCheck_1789_ == 0 {
                            v___x_1784_ = v___x_1763_;
                            v_isShared_1785_ = v_isSharedCheck_1789_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1782_);
                            crate::leanh::lean_dec(v___x_1763_);
                            v___x_1784_ = crate::leanh::lean_box(0);
                            v_isShared_1785_ = v_isSharedCheck_1789_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_declName_1718_);
                v___x_1726_ =
                    l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline(
                        v_declName_1718_,
                        v___y_1724_,
                        v___y_1725_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1726_) == 0 {
                    v_a_1727_ = crate::leanh::lean_ctor_get(v___x_1726_, 0);
                    v_isSharedCheck_1743_ = (!crate::leanh::lean_is_exclusive(v___x_1726_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1729_ = v___x_1726_;
                        v_isShared_1730_ = v_isSharedCheck_1743_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1727_);
                        crate::leanh::lean_dec(v___x_1726_);
                        v___x_1729_ = crate::leanh::lean_box(0);
                        v_isShared_1730_ = v_isSharedCheck_1743_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_1718_);
                    v_a_1744_ = crate::leanh::lean_ctor_get(v___x_1726_, 0);
                    v_isSharedCheck_1751_ = (!crate::leanh::lean_is_exclusive(v___x_1726_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1746_ = v___x_1726_;
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1744_);
                        crate::leanh::lean_dec(v___x_1726_);
                        v___x_1746_ = crate::leanh::lean_box(0);
                        v_isShared_1747_ = v_isSharedCheck_1751_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1731_ = (crate::leanh::lean_unbox(v_a_1727_) as u8);
                if v___x_1731_ == 0 {
                    crate::leanh::lean_del_object(v___x_1729_);
                    v___x_1732_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_);
                    v___x_1733_ = (crate::leanh::lean_unbox(v_a_1727_) as u8);
                    crate::leanh::lean_dec(v_a_1727_);
                    v___x_1734_ = l_Lean_MessageData_ofConstName(v_declName_1718_, v___x_1733_);
                    v___x_1735_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1732_);
                    crate::leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
                    v___x_1736_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__3_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_);
                    v___x_1737_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1737_, 0, v___x_1735_);
                    crate::leanh::lean_ctor_set(v___x_1737_, 1, v___x_1736_);
                    v___x_1738_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v___x_1737_, v___y_1724_, v___y_1725_);
                    return v___x_1738_;
                } else {
                    crate::leanh::lean_dec(v_a_1727_);
                    crate::leanh::lean_dec(v_declName_1718_);
                    v___x_1739_ = crate::leanh::lean_box(0);
                    if v_isShared_1730_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1729_, 0, v___x_1739_);
                        v___x_1741_ = v___x_1729_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1742_, 0, v___x_1739_);
                        v___x_1741_ = v_reuseFailAlloc_1742_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1741_;
            }
            4 => {
                if v_isShared_1747_ == 0 {
                    v___x_1749_ = v___x_1746_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_a_1744_);
                    v___x_1749_ = v_reuseFailAlloc_1750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1749_;
            }
            6 => {
                v___x_1770_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__8_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
                v___x_1771_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_InlineAttributeKind_toAttrString(v_kind_1719_);
                v___x_1772_ = lean_string_append(v___x_1770_, v___x_1771_);
                crate::leanh::lean_dec_ref(v___x_1771_);
                v___x_1773_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1___closed__9_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
                v___x_1774_ = lean_string_append(v___x_1772_, v___x_1773_);
                v___x_1775_ = lean_string_append(v___x_1774_, v_a_1766_);
                crate::leanh::lean_dec(v_a_1766_);
                if v_isShared_1769_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1768_, 0, v___x_1775_);
                    v___x_1777_ = v___x_1768_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1779_, 0, v___x_1775_);
                    v___x_1777_ = v_reuseFailAlloc_1779_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1778_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___redArg(v___x_1777_, v___y_1720_, v___y_1721_);
                return v___x_1778_;
            }
            8 => {
                if v_isShared_1785_ == 0 {
                    v___x_1787_ = v___x_1784_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1788_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
                    v___x_1787_ = v_reuseFailAlloc_1788_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1787_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2____boxed(
    mut v___f_1790_: *mut crate::leanh::LeanObject,
    mut v_declName_1791_: *mut crate::leanh::LeanObject,
    mut v_kind_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1796_: u8 = 0;
    let mut v_res_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1796_ = (crate::leanh::lean_unbox(v_kind_1792_) as u8);
    v_res_1797_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___lam__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_(v___f_1790_, v_declName_1791_, v_kind_boxed_1796_, v___y_1793_, v___y_1794_);
    crate::leanh::lean_dec(v___y_1794_);
    crate::leanh::lean_dec_ref(v___y_1793_);
    return v_res_1797_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___f_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: u8 = 0;
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1874_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__1_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1875_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__26_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1876_ = 0;
    v___x_1877_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1878_ =
        l_Lean_registerEnumAttributes___redArg(v___x_1875_, v___f_1874_, v___x_1876_, v___x_1877_);
    return v___x_1878_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2____boxed(
    mut v_a_1879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1880_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_();
    return v_res_1880_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03b1_1881_: *mut crate::leanh::LeanObject,
    mut v_x_1882_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1883_: u8,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1887_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_1882_, v_isExporting_1883_, v___y_1884_, v___y_1885_);
    return v___x_1887_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03b1_1888_: *mut crate::leanh::LeanObject,
    mut v_x_1889_: *mut crate::leanh::LeanObject,
    mut v_isExporting_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_1894_: u8 = 0;
    let mut v_res_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_1894_ = (crate::leanh::lean_unbox(v_isExporting_1890_) as u8);
    v_res_1895_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b1_1888_, v_x_1889_, v_isExporting_boxed_1894_, v___y_1891_, v___y_1892_);
    crate::leanh::lean_dec(v___y_1892_);
    crate::leanh::lean_dec_ref(v___y_1891_);
    return v_res_1895_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_1896_: *mut crate::leanh::LeanObject,
    mut v_x_1897_: *mut crate::leanh::LeanObject,
    mut v_when_1898_: u8,
    mut v___y_1899_: *mut crate::leanh::LeanObject,
    mut v___y_1900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1902_ = l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0___redArg(v_x_1897_, v_when_1898_, v___y_1899_, v___y_1900_);
    return v___x_1902_;
}
pub unsafe fn l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_1903_: *mut crate::leanh::LeanObject,
    mut v_x_1904_: *mut crate::leanh::LeanObject,
    mut v_when_1905_: *mut crate::leanh::LeanObject,
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v___y_1907_: *mut crate::leanh::LeanObject,
    mut v___y_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_1909_: u8 = 0;
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_1909_ = (crate::leanh::lean_unbox(v_when_1905_) as u8);
    v_res_1910_ = l_Lean_withoutExporting___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__0(v_00_u03b1_1903_, v_x_1904_, v_when_boxed_1909_, v___y_1906_, v___y_1907_);
    crate::leanh::lean_dec(v___y_1907_);
    crate::leanh::lean_dec_ref(v___y_1906_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1(
    mut v_00_u03b1_1911_: *mut crate::leanh::LeanObject,
    mut v_x_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1916_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___redArg(v_x_1912_, v___y_1913_, v___y_1914_);
    return v___x_1916_;
}
pub unsafe fn l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1___boxed(
    mut v_00_u03b1_1917_: *mut crate::leanh::LeanObject,
    mut v_x_1918_: *mut crate::leanh::LeanObject,
    mut v___y_1919_: *mut crate::leanh::LeanObject,
    mut v___y_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1922_ = l_Lean_ofExcept___at___00__private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2__spec__1(v_00_u03b1_1917_, v_x_1918_, v___y_1919_, v___y_1920_);
    crate::leanh::lean_dec(v___y_1920_);
    crate::leanh::lean_dec_ref(v___y_1919_);
    return v_res_1922_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1925_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1926_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1___closed__0;
    v___x_1927_ = l_Lean_addBuiltinDocString(v___x_1925_, v___x_1926_);
    return v___x_1927_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1___boxed(
    mut v_a_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1();
    return v_res_1929_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1956_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn___closed__30_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_;
    v___x_1957_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___closed__6;
    v___x_1958_ = l_Lean_addBuiltinDeclarationRanges(v___x_1956_, v___x_1957_);
    return v___x_1958_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3___boxed(
    mut v_a_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3();
    return v_res_1960_;
}
pub unsafe fn l_Lean_Compiler_setInlineAttribute(
    mut v_env_1961_: *mut crate::leanh::LeanObject,
    mut v_declName_1962_: *mut crate::leanh::LeanObject,
    mut v_kind_1963_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_Compiler_inlineAttrs;
    v___x_1965_ = crate::leanh::lean_box((v_kind_1963_) as usize);
    v___x_1966_ = l_Lean_EnumAttributes_setValue___redArg(
        v___x_1964_,
        v_env_1961_,
        v_declName_1962_,
        v___x_1965_,
    );
    return v___x_1966_;
}
pub unsafe fn l_Lean_Compiler_setInlineAttribute___boxed(
    mut v_env_1967_: *mut crate::leanh::LeanObject,
    mut v_declName_1968_: *mut crate::leanh::LeanObject,
    mut v_kind_1969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1970_: u8 = 0;
    let mut v_res_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1970_ = (crate::leanh::lean_unbox(v_kind_1969_) as u8);
    v_res_1971_ =
        l_Lean_Compiler_setInlineAttribute(v_env_1967_, v_declName_1968_, v_kind_boxed_1970_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_Compiler_getInlineAttribute_x3f(
    mut v_env_1972_: *mut crate::leanh::LeanObject,
    mut v_declName_1973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1974_: u8 = 0;
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1974_ = 0;
    v___x_1975_ = l_Lean_Compiler_inlineAttrs;
    v___x_1976_ = crate::leanh::lean_box((v___x_1974_) as usize);
    v___x_1977_ = l_Lean_EnumAttributes_getValue___redArg(
        v___x_1976_,
        v___x_1975_,
        v_env_1972_,
        v_declName_1973_,
    );
    return v___x_1977_;
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
    mut v_env_1978_: *mut crate::leanh::LeanObject,
    mut v_kind_1979_: u8,
    mut v_declName_1980_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1981_: u8 = 0;
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1981_ = 0;
    v___x_1982_ = l_Lean_Compiler_inlineAttrs;
    v___x_1983_ = crate::leanh::lean_box((v___x_1981_) as usize);
    v___x_1984_ = l_Lean_EnumAttributes_getValue___redArg(
        v___x_1983_,
        v___x_1982_,
        v_env_1978_,
        v_declName_1980_,
    );
    if crate::leanh::lean_obj_tag(v___x_1984_) == 1 {
        let mut v_val_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1986_: u8 = 0;
        let mut v___x_1987_: u8 = 0;
        v_val_1985_ = crate::leanh::lean_ctor_get(v___x_1984_, 0);
        crate::leanh::lean_inc(v_val_1985_);
        crate::leanh::lean_dec_ref_known(v___x_1984_, 1);
        v___x_1986_ = (crate::leanh::lean_unbox(v_val_1985_) as u8);
        crate::leanh::lean_dec(v_val_1985_);
        v___x_1987_ = l_Lean_Compiler_instBEqInlineAttributeKind_beq(v_kind_1979_, v___x_1986_);
        return v___x_1987_;
    } else {
        let mut v___x_1988_: u8 = 0;
        crate::leanh::lean_dec(v___x_1984_);
        v___x_1988_ = 0;
        return v___x_1988_;
    }
}
pub unsafe fn l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore___boxed(
    mut v_env_1989_: *mut crate::leanh::LeanObject,
    mut v_kind_1990_: *mut crate::leanh::LeanObject,
    mut v_declName_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_1992_: u8 = 0;
    let mut v_res_1993_: u8 = 0;
    let mut v_r_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_1992_ = (crate::leanh::lean_unbox(v_kind_1990_) as u8);
    v_res_1993_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
        v_env_1989_,
        v_kind_boxed_1992_,
        v_declName_1991_,
    );
    v_r_1994_ = crate::leanh::lean_box((v_res_1993_) as usize);
    return v_r_1994_;
}
pub unsafe fn l_Lean_Compiler_hasInlineAttribute(
    mut v_env_1995_: *mut crate::leanh::LeanObject,
    mut v_declName_1996_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1997_: u8 = 0;
    let mut v___x_1998_: u8 = 0;
    v___x_1997_ = 0;
    v___x_1998_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
        v_env_1995_,
        v___x_1997_,
        v_declName_1996_,
    );
    return v___x_1998_;
}
pub unsafe fn l_Lean_Compiler_hasInlineAttribute___boxed(
    mut v_env_1999_: *mut crate::leanh::LeanObject,
    mut v_declName_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2001_: u8 = 0;
    let mut v_r_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2001_ = l_Lean_Compiler_hasInlineAttribute(v_env_1999_, v_declName_2000_);
    v_r_2002_ = crate::leanh::lean_box((v_res_2001_) as usize);
    return v_r_2002_;
}
pub unsafe fn l_Lean_Compiler_hasInlineIfReduceAttribute(
    mut v_env_2003_: *mut crate::leanh::LeanObject,
    mut v_declName_2004_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2005_: u8 = 0;
    let mut v___x_2006_: u8 = 0;
    v___x_2005_ = 3;
    v___x_2006_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
        v_env_2003_,
        v___x_2005_,
        v_declName_2004_,
    );
    return v___x_2006_;
}
pub unsafe fn l_Lean_Compiler_hasInlineIfReduceAttribute___boxed(
    mut v_env_2007_: *mut crate::leanh::LeanObject,
    mut v_declName_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2009_: u8 = 0;
    let mut v_r_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2009_ = l_Lean_Compiler_hasInlineIfReduceAttribute(v_env_2007_, v_declName_2008_);
    v_r_2010_ = crate::leanh::lean_box((v_res_2009_) as usize);
    return v_r_2010_;
}
pub unsafe fn l_Lean_Compiler_hasNoInlineAttribute(
    mut v_env_2011_: *mut crate::leanh::LeanObject,
    mut v_declName_2012_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2013_: u8 = 0;
    let mut v___x_2014_: u8 = 0;
    v___x_2013_ = 1;
    v___x_2014_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
        v_env_2011_,
        v___x_2013_,
        v_declName_2012_,
    );
    return v___x_2014_;
}
pub unsafe fn l_Lean_Compiler_hasNoInlineAttribute___boxed(
    mut v_env_2015_: *mut crate::leanh::LeanObject,
    mut v_declName_2016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2017_: u8 = 0;
    let mut v_r_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2017_ = l_Lean_Compiler_hasNoInlineAttribute(v_env_2015_, v_declName_2016_);
    v_r_2018_ = crate::leanh::lean_box((v_res_2017_) as usize);
    return v_r_2018_;
}
pub unsafe fn l_Lean_Compiler_hasMacroInlineAttribute(
    mut v_env_2019_: *mut crate::leanh::LeanObject,
    mut v_declName_2020_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2021_: u8 = 0;
    let mut v___x_2022_: u8 = 0;
    v___x_2021_ = 2;
    v___x_2022_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
        v_env_2019_,
        v___x_2021_,
        v_declName_2020_,
    );
    return v___x_2022_;
}
pub unsafe fn l_Lean_Compiler_hasMacroInlineAttribute___boxed(
    mut v_env_2023_: *mut crate::leanh::LeanObject,
    mut v_declName_2024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2025_: u8 = 0;
    let mut v_r_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2025_ = l_Lean_Compiler_hasMacroInlineAttribute(v_env_2023_, v_declName_2024_);
    v_r_2026_ = crate::leanh::lean_box((v_res_2025_) as usize);
    return v_r_2026_;
}
pub unsafe fn l_Lean_Compiler_hasAlwaysInlineAttribute(
    mut v_env_2027_: *mut crate::leanh::LeanObject,
    mut v_declName_2028_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: u8 = 0;
    v___x_2029_ = 4;
    v___x_2030_ = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_hasInlineAttrCore(
        v_env_2027_,
        v___x_2029_,
        v_declName_2028_,
    );
    return v___x_2030_;
}
pub unsafe fn l_Lean_Compiler_hasAlwaysInlineAttribute___boxed(
    mut v_env_2031_: *mut crate::leanh::LeanObject,
    mut v_declName_2032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2033_: u8 = 0;
    let mut v_r_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2033_ = l_Lean_Compiler_hasAlwaysInlineAttribute(v_env_2031_, v_declName_2032_);
    v_r_2034_ = crate::leanh::lean_box((v_res_2033_) as usize);
    return v_r_2034_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_InlineAttrs(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_RecExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Compiler_instInhabitedInlineAttributeKind_default =
        _init_l_Lean_Compiler_instInhabitedInlineAttributeKind_default();
    l_Lean_Compiler_instInhabitedInlineAttributeKind =
        _init_l_Lean_Compiler_instInhabitedInlineAttributeKind();
    res = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_initFn_00___x40_Lean_Compiler_InlineAttrs_1525986753____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_inlineAttrs = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Compiler_inlineAttrs);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_inlineAttrs___regBuiltin_Lean_Compiler_inlineAttrs_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_InlineAttrs(
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
pub unsafe fn initialize_Lean_Compiler_InlineAttrs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Attributes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_RecExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_InlineAttrs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_InlineAttrs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_InlineAttrs(builtin);
}
