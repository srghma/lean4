// Lean compiler output
// Module: Lean.Elab.Tactic.DiscrTreeKey
// Imports: Lean.Elab.Command Lean.Meta.Tactic.Simp.SimpTheorems
use crate::ffi::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_uint64_lor, lean_uint64_shift_left,
    lean_uint64_shift_right,
};
use crate::r#gen::Init::Meta::Defs::l_Lean_TSyntax_getId;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Term::TermElabM::l_Lean_Elab_Term_elabTerm;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_isAppOfArity,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_findFromUserName_x3f, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEq;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaTelescopeReducing, l_Lean_Meta_whnfR,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::l_Lean_Meta_DiscrTree_keysAsPattern;
use crate::r#gen::Lean::Meta::DiscrTree::Main::l_Lean_Meta_DiscrTree_mkPath;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    initialize_Lean_Meta_Tactic_Simp_SimpTheorems, l_Lean_Meta_simpGlobalConfig,
    runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1_value) as *mut leanh::LeanObject,9917798623386220051 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [78, 101, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3_value) as *mut leanh::LeanObject,6695605208187598753 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5_value) as *mut leanh::LeanObject,16612019923665488825 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7_value) as *mut leanh::LeanObject,16122875713692181903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0_value) as *mut leanh::LeanObject,5117844058249666356 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value: leanh::LeanStringObject<17> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7_value) as *mut leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value:
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
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        100, 105, 115, 99, 114, 84, 114, 101, 101, 75, 101, 121, 67, 109, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2_value)
            as *mut leanh::LeanObject,
        56916842056113140 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 75, 101, 121, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1_value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 118, 97, 108, 68, 105, 115, 99, 114, 84, 114, 101, 101, 75, 101, 121, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value) as *mut leanh::LeanObject,15507137722572484428 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1_value) as *mut leanh::LeanObject,17543557265682499791 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0_value:
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
        100, 105, 115, 99, 114, 84, 114, 101, 101, 83, 105, 109, 112, 75, 101, 121, 67, 109, 100, 0,
    ],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0_value
        ) as *mut leanh::LeanObject,
        15128410572378117509 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [101, 118, 97, 108, 68, 105, 115, 99, 114, 84, 114, 101, 101, 83, 105, 109, 112, 75, 101, 121, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value) as *mut leanh::LeanObject,12733524109236233889 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value) as *mut leanh::LeanObject,15507137722572484428 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0_value) as *mut leanh::LeanObject,16162822488894939254 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0()
-> u64 {
    let mut v___x_1259_: u8 = 0;
    let mut v___x_1260_: u64 = 0;
    v___x_1259_ = 2;
    v___x_1260_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1259_);
    return v___x_1260_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(
    mut v_e_1273_: *mut leanh::LeanObject,
    mut v_simp_1274_: u8,
    mut v_a_1275_: *mut leanh::LeanObject,
    mut v_a_1276_: *mut leanh::LeanObject,
    mut v_a_1277_: *mut leanh::LeanObject,
    mut v_a_1278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1281_: u8 = 0;
    let mut v_ctxApprox_1282_: u8 = 0;
    let mut v_quasiPatternApprox_1283_: u8 = 0;
    let mut v_constApprox_1284_: u8 = 0;
    let mut v_isDefEqStuckEx_1285_: u8 = 0;
    let mut v_unificationHints_1286_: u8 = 0;
    let mut v_proofIrrelevance_1287_: u8 = 0;
    let mut v_assignSyntheticOpaque_1288_: u8 = 0;
    let mut v_offsetCnstrs_1289_: u8 = 0;
    let mut v_etaStruct_1290_: u8 = 0;
    let mut v_univApprox_1291_: u8 = 0;
    let mut v_iota_1292_: u8 = 0;
    let mut v_beta_1293_: u8 = 0;
    let mut v_proj_1294_: u8 = 0;
    let mut v_zeta_1295_: u8 = 0;
    let mut v_zetaDelta_1296_: u8 = 0;
    let mut v_zetaUnused_1297_: u8 = 0;
    let mut v_zetaHave_1298_: u8 = 0;
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v_trackZetaDelta_1302_: u8 = 0;
    let mut v_zetaDeltaSet_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1309_: u8 = 0;
    let mut v_inTypeClassResolution_1310_: u8 = 0;
    let mut v_cacheInferType_1311_: u8 = 0;
    let mut v___x_1312_: u8 = 0;
    let mut v_config_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u64 = 0;
    let mut v___x_1316_: u64 = 0;
    let mut v___x_1317_: u64 = 0;
    let mut v___x_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: u64 = 0;
    let mut v___x_1321_: u64 = 0;
    let mut v_key_1322_: u64 = 0;
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v_snd_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u64 = 0;
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1398_: u8 = 0;
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut v_unused_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_unused_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_reuseFailAlloc_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1280_ = l_Lean_Meta_Context_config(v_a_1275_);
                v_foApprox_1281_ = leanh::lean_ctor_get_uint8(v___x_1280_, 0 as u32);
                v_ctxApprox_1282_ = leanh::lean_ctor_get_uint8(v___x_1280_, 1 as u32);
                v_quasiPatternApprox_1283_ =
                    leanh::lean_ctor_get_uint8(v___x_1280_, 2 as u32);
                v_constApprox_1284_ = leanh::lean_ctor_get_uint8(v___x_1280_, 3 as u32);
                v_isDefEqStuckEx_1285_ = leanh::lean_ctor_get_uint8(v___x_1280_, 4 as u32);
                v_unificationHints_1286_ = leanh::lean_ctor_get_uint8(v___x_1280_, 5 as u32);
                v_proofIrrelevance_1287_ = leanh::lean_ctor_get_uint8(v___x_1280_, 6 as u32);
                v_assignSyntheticOpaque_1288_ =
                    leanh::lean_ctor_get_uint8(v___x_1280_, 7 as u32);
                v_offsetCnstrs_1289_ = leanh::lean_ctor_get_uint8(v___x_1280_, 8 as u32);
                v_etaStruct_1290_ = leanh::lean_ctor_get_uint8(v___x_1280_, 10 as u32);
                v_univApprox_1291_ = leanh::lean_ctor_get_uint8(v___x_1280_, 11 as u32);
                v_iota_1292_ = leanh::lean_ctor_get_uint8(v___x_1280_, 12 as u32);
                v_beta_1293_ = leanh::lean_ctor_get_uint8(v___x_1280_, 13 as u32);
                v_proj_1294_ = leanh::lean_ctor_get_uint8(v___x_1280_, 14 as u32);
                v_zeta_1295_ = leanh::lean_ctor_get_uint8(v___x_1280_, 15 as u32);
                v_zetaDelta_1296_ = leanh::lean_ctor_get_uint8(v___x_1280_, 16 as u32);
                v_zetaUnused_1297_ = leanh::lean_ctor_get_uint8(v___x_1280_, 17 as u32);
                v_zetaHave_1298_ = leanh::lean_ctor_get_uint8(v___x_1280_, 18 as u32);
                v_isSharedCheck_1416_ = (!leanh::lean_is_exclusive(v___x_1280_)) as u8;
                if v_isSharedCheck_1416_ == 0 {
                    v___x_1300_ = v___x_1280_;
                    v_isShared_1301_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1280_);
                    v___x_1300_ = leanh::lean_box(0);
                    v_isShared_1301_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_1302_ = leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1303_ = leanh::lean_ctor_get(v_a_1275_, 1);
                v_lctx_1304_ = leanh::lean_ctor_get(v_a_1275_, 2);
                v_localInstances_1305_ = leanh::lean_ctor_get(v_a_1275_, 3);
                v_defEqCtx_x3f_1306_ = leanh::lean_ctor_get(v_a_1275_, 4);
                v_synthPendingDepth_1307_ = leanh::lean_ctor_get(v_a_1275_, 5);
                v_canUnfold_x3f_1308_ = leanh::lean_ctor_get(v_a_1275_, 6);
                v_univApprox_1309_ = leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1310_ = leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1311_ = leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1312_ = 2;
                if v_isShared_1301_ == 0 {
                    v_config_1314_ = v___x_1300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        0 as u32,
                        v_foApprox_1281_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        1 as u32,
                        v_ctxApprox_1282_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        2 as u32,
                        v_quasiPatternApprox_1283_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        3 as u32,
                        v_constApprox_1284_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        4 as u32,
                        v_isDefEqStuckEx_1285_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        5 as u32,
                        v_unificationHints_1286_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        6 as u32,
                        v_proofIrrelevance_1287_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        7 as u32,
                        v_assignSyntheticOpaque_1288_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        8 as u32,
                        v_offsetCnstrs_1289_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        10 as u32,
                        v_etaStruct_1290_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        11 as u32,
                        v_univApprox_1291_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        12 as u32,
                        v_iota_1292_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        13 as u32,
                        v_beta_1293_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        14 as u32,
                        v_proj_1294_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        15 as u32,
                        v_zeta_1295_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        16 as u32,
                        v_zetaDelta_1296_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        17 as u32,
                        v_zetaUnused_1297_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        18 as u32,
                        v_zetaHave_1298_,
                    );
                    v_config_1314_ = v_reuseFailAlloc_1415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(v_config_1314_, 9 as u32, v___x_1312_);
                v___x_1315_ = l_Lean_Meta_Context_configKey(v_a_1275_);
                v___x_1316_ = 3u64;
                v___x_1317_ = lean_uint64_shift_right(v___x_1315_, v___x_1316_);
                v___x_1318_ = leanh::lean_box(0);
                v___x_1319_ = 0;
                v___x_1320_ = lean_uint64_shift_left(v___x_1317_, v___x_1316_);
                v___x_1321_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0_once), _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0);
                v_key_1322_ = lean_uint64_lor(v___x_1320_, v___x_1321_);
                v___x_1323_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_1323_, 0, v_config_1314_);
                leanh::lean_ctor_set_uint64(
                    v___x_1323_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_key_1322_,
                );
                leanh::lean_inc(v_canUnfold_x3f_1308_);
                leanh::lean_inc(v_synthPendingDepth_1307_);
                leanh::lean_inc(v_defEqCtx_x3f_1306_);
                leanh::lean_inc_ref(v_localInstances_1305_);
                leanh::lean_inc_ref(v_lctx_1304_);
                leanh::lean_inc(v_zetaDeltaSet_1303_);
                v___x_1324_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                leanh::lean_ctor_set(v___x_1324_, 1, v_zetaDeltaSet_1303_);
                leanh::lean_ctor_set(v___x_1324_, 2, v_lctx_1304_);
                leanh::lean_ctor_set(v___x_1324_, 3, v_localInstances_1305_);
                leanh::lean_ctor_set(v___x_1324_, 4, v_defEqCtx_x3f_1306_);
                leanh::lean_ctor_set(v___x_1324_, 5, v_synthPendingDepth_1307_);
                leanh::lean_ctor_set(v___x_1324_, 6, v_canUnfold_x3f_1308_);
                leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1302_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1309_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1310_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1311_,
                );
                v___x_1325_ = l_Lean_Meta_forallMetaTelescopeReducing(
                    v_e_1273_,
                    v___x_1318_,
                    v___x_1319_,
                    v___x_1324_,
                    v_a_1276_,
                    v_a_1277_,
                    v_a_1278_,
                );
                leanh::lean_dec_ref_known(v___x_1324_, 7);
                if leanh::lean_obj_tag(v___x_1325_) == 0 {
                    v_a_1326_ = leanh::lean_ctor_get(v___x_1325_, 0);
                    leanh::lean_inc(v_a_1326_);
                    leanh::lean_dec_ref_known(v___x_1325_, 1);
                    v_snd_1327_ = leanh::lean_ctor_get(v_a_1326_, 1);
                    v_isSharedCheck_1405_ = (!leanh::lean_is_exclusive(v_a_1326_)) as u8;
                    if v_isSharedCheck_1405_ == 0 {
                        v_unused_1406_ = leanh::lean_ctor_get(v_a_1326_, 0);
                        leanh::lean_dec(v_unused_1406_);
                        v___x_1329_ = v_a_1326_;
                        v_isShared_1330_ = v_isSharedCheck_1405_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1327_);
                        leanh::lean_dec(v_a_1326_);
                        v___x_1329_ = leanh::lean_box(0);
                        v_isShared_1330_ = v_isSharedCheck_1405_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1407_ = leanh::lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1414_ = (!leanh::lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v___x_1409_ = v___x_1325_;
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1407_);
                        leanh::lean_dec(v___x_1325_);
                        v___x_1409_ = leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_1331_ = leanh::lean_ctor_get(v_snd_1327_, 1);
                v_isSharedCheck_1403_ = (!leanh::lean_is_exclusive(v_snd_1327_)) as u8;
                if v_isSharedCheck_1403_ == 0 {
                    v_unused_1404_ = leanh::lean_ctor_get(v_snd_1327_, 0);
                    leanh::lean_dec(v_unused_1404_);
                    v___x_1333_ = v_snd_1327_;
                    v_isShared_1334_ = v_isSharedCheck_1403_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1331_);
                    leanh::lean_dec(v_snd_1327_);
                    v___x_1333_ = leanh::lean_box(0);
                    v_isShared_1334_ = v_isSharedCheck_1403_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1335_ =
                    l_Lean_Meta_whnfR(v_snd_1331_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
                if leanh::lean_obj_tag(v___x_1335_) == 0 {
                    v_a_1336_ = leanh::lean_ctor_get(v___x_1335_, 0);
                    leanh::lean_inc(v_a_1336_);
                    leanh::lean_dec_ref_known(v___x_1335_, 1);
                    if v_simp_1274_ == 0 {
                        leanh::lean_del_object(v___x_1333_);
                        leanh::lean_del_object(v___x_1329_);
                        v___x_1379_ = l_Lean_Meta_DiscrTree_mkPath(
                            v_a_1336_,
                            v_simp_1274_,
                            v_a_1275_,
                            v_a_1276_,
                            v_a_1277_,
                            v_a_1278_,
                        );
                        return v___x_1379_;
                    } else {
                        v___x_1380_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8;
                        v___x_1381_ = leanh::lean_unsigned_to_nat(3);
                        v___x_1382_ = l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1380_, v___x_1381_);
                        if v___x_1382_ == 0 {
                            leanh::lean_del_object(v___x_1333_);
                            leanh::lean_del_object(v___x_1329_);
                            v___y_1338_ = v___x_1318_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1383_ = l_Lean_Expr_appFn_x21(v_a_1336_);
                            v___x_1384_ = l_Lean_Expr_appFn_x21(v___x_1383_);
                            v___x_1385_ = l_Lean_Expr_appArg_x21(v___x_1384_);
                            leanh::lean_dec_ref(v___x_1384_);
                            v___x_1386_ = l_Lean_Expr_appArg_x21(v___x_1383_);
                            leanh::lean_dec_ref(v___x_1383_);
                            v___x_1387_ = l_Lean_Expr_appArg_x21(v_a_1336_);
                            if v_isShared_1334_ == 0 {
                                leanh::lean_ctor_set(v___x_1333_, 1, v___x_1387_);
                                leanh::lean_ctor_set(v___x_1333_, 0, v___x_1386_);
                                v___x_1389_ = v___x_1333_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1394_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1386_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1387_);
                                v___x_1389_ = v_reuseFailAlloc_1394_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_1333_);
                    leanh::lean_del_object(v___x_1329_);
                    v_a_1395_ = leanh::lean_ctor_get(v___x_1335_, 0);
                    v_isSharedCheck_1402_ = (!leanh::lean_is_exclusive(v___x_1335_)) as u8;
                    if v_isSharedCheck_1402_ == 0 {
                        v___x_1397_ = v___x_1335_;
                        v_isShared_1398_ = v_isSharedCheck_1402_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1395_);
                        leanh::lean_dec(v___x_1335_);
                        v___x_1397_ = leanh::lean_box(0);
                        v_isShared_1398_ = v_isSharedCheck_1402_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1339_ = l_Lean_Meta_simpGlobalConfig;
                v_config_1340_ = leanh::lean_ctor_get(v___x_1339_, 0);
                v___x_1341_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1340_);
                leanh::lean_inc_ref(v_config_1340_);
                v___x_1342_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                leanh::lean_ctor_set(v___x_1342_, 0, v_config_1340_);
                leanh::lean_ctor_set_uint64(
                    v___x_1342_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1341_,
                );
                leanh::lean_inc(v_canUnfold_x3f_1308_);
                leanh::lean_inc(v_synthPendingDepth_1307_);
                leanh::lean_inc(v_defEqCtx_x3f_1306_);
                leanh::lean_inc_ref(v_localInstances_1305_);
                leanh::lean_inc_ref(v_lctx_1304_);
                leanh::lean_inc(v_zetaDeltaSet_1303_);
                v___x_1343_ = leanh::lean_alloc_ctor(0, 7, (4) as u32);
                leanh::lean_ctor_set(v___x_1343_, 0, v___x_1342_);
                leanh::lean_ctor_set(v___x_1343_, 1, v_zetaDeltaSet_1303_);
                leanh::lean_ctor_set(v___x_1343_, 2, v_lctx_1304_);
                leanh::lean_ctor_set(v___x_1343_, 3, v_localInstances_1305_);
                leanh::lean_ctor_set(v___x_1343_, 4, v_defEqCtx_x3f_1306_);
                leanh::lean_ctor_set(v___x_1343_, 5, v_synthPendingDepth_1307_);
                leanh::lean_ctor_set(v___x_1343_, 6, v_canUnfold_x3f_1308_);
                leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1302_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1309_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1310_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1311_,
                );
                if leanh::lean_obj_tag(v___y_1338_) == 1 {
                    leanh::lean_dec(v_a_1336_);
                    v_val_1344_ = leanh::lean_ctor_get(v___y_1338_, 0);
                    leanh::lean_inc(v_val_1344_);
                    leanh::lean_dec_ref_known(v___y_1338_, 1);
                    v_snd_1345_ = leanh::lean_ctor_get(v_val_1344_, 1);
                    leanh::lean_inc(v_snd_1345_);
                    leanh::lean_dec(v_val_1344_);
                    v_fst_1346_ = leanh::lean_ctor_get(v_snd_1345_, 0);
                    leanh::lean_inc(v_fst_1346_);
                    leanh::lean_dec(v_snd_1345_);
                    v___x_1347_ = 0;
                    v___x_1348_ = l_Lean_Meta_DiscrTree_mkPath(
                        v_fst_1346_,
                        v___x_1347_,
                        v___x_1343_,
                        v_a_1276_,
                        v_a_1277_,
                        v_a_1278_,
                    );
                    leanh::lean_dec_ref_known(v___x_1343_, 7);
                    return v___x_1348_;
                } else {
                    leanh::lean_dec(v___y_1338_);
                    v___x_1349_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2;
                    v___x_1350_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1351_ = l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1349_, v___x_1350_);
                    if v___x_1351_ == 0 {
                        v___x_1352_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4;
                        v___x_1353_ = leanh::lean_unsigned_to_nat(3);
                        v___x_1354_ = l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1352_, v___x_1353_);
                        if v___x_1354_ == 0 {
                            v___x_1355_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6;
                            v___x_1356_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1357_ =
                                l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1355_, v___x_1356_);
                            if v___x_1357_ == 0 {
                                v___x_1358_ = l_Lean_Meta_DiscrTree_mkPath(
                                    v_a_1336_,
                                    v___x_1357_,
                                    v___x_1343_,
                                    v_a_1276_,
                                    v_a_1277_,
                                    v_a_1278_,
                                );
                                leanh::lean_dec_ref_known(v___x_1343_, 7);
                                return v___x_1358_;
                            } else {
                                v___x_1359_ = l_Lean_Expr_appArg_x21(v_a_1336_);
                                leanh::lean_dec(v_a_1336_);
                                v___x_1360_ = l_Lean_Meta_DiscrTree_mkPath(
                                    v___x_1359_,
                                    v___x_1354_,
                                    v___x_1343_,
                                    v_a_1276_,
                                    v_a_1277_,
                                    v_a_1278_,
                                );
                                leanh::lean_dec_ref_known(v___x_1343_, 7);
                                return v___x_1360_;
                            }
                        } else {
                            v___x_1361_ = l_Lean_Expr_appFn_x21(v_a_1336_);
                            v___x_1362_ = l_Lean_Expr_appArg_x21(v___x_1361_);
                            leanh::lean_dec_ref(v___x_1361_);
                            v___x_1363_ = l_Lean_Expr_appArg_x21(v_a_1336_);
                            leanh::lean_dec(v_a_1336_);
                            v___x_1364_ = l_Lean_Meta_mkEq(
                                v___x_1362_,
                                v___x_1363_,
                                v___x_1343_,
                                v_a_1276_,
                                v_a_1277_,
                                v_a_1278_,
                            );
                            if leanh::lean_obj_tag(v___x_1364_) == 0 {
                                v_a_1365_ = leanh::lean_ctor_get(v___x_1364_, 0);
                                leanh::lean_inc(v_a_1365_);
                                leanh::lean_dec_ref_known(v___x_1364_, 1);
                                v___x_1366_ = l_Lean_Meta_DiscrTree_mkPath(
                                    v_a_1365_,
                                    v___x_1351_,
                                    v___x_1343_,
                                    v_a_1276_,
                                    v_a_1277_,
                                    v_a_1278_,
                                );
                                leanh::lean_dec_ref_known(v___x_1343_, 7);
                                return v___x_1366_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_1343_, 7);
                                v_a_1367_ = leanh::lean_ctor_get(v___x_1364_, 0);
                                v_isSharedCheck_1374_ =
                                    (!leanh::lean_is_exclusive(v___x_1364_)) as u8;
                                if v_isSharedCheck_1374_ == 0 {
                                    v___x_1369_ = v___x_1364_;
                                    v_isShared_1370_ = v_isSharedCheck_1374_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1367_);
                                    leanh::lean_dec(v___x_1364_);
                                    v___x_1369_ = leanh::lean_box(0);
                                    v_isShared_1370_ = v_isSharedCheck_1374_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1375_ = l_Lean_Expr_appFn_x21(v_a_1336_);
                        leanh::lean_dec(v_a_1336_);
                        v___x_1376_ = l_Lean_Expr_appArg_x21(v___x_1375_);
                        leanh::lean_dec_ref(v___x_1375_);
                        v___x_1377_ = 0;
                        v___x_1378_ = l_Lean_Meta_DiscrTree_mkPath(
                            v___x_1376_,
                            v___x_1377_,
                            v___x_1343_,
                            v_a_1276_,
                            v_a_1277_,
                            v_a_1278_,
                        );
                        leanh::lean_dec_ref_known(v___x_1343_, 7);
                        return v___x_1378_;
                    }
                }
            }
            6 => {
                if v_isShared_1370_ == 0 {
                    v___x_1372_ = v___x_1369_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
                    v___x_1372_ = v_reuseFailAlloc_1373_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1372_;
            }
            8 => {
                if v_isShared_1330_ == 0 {
                    leanh::lean_ctor_set(v___x_1329_, 1, v___x_1389_);
                    leanh::lean_ctor_set(v___x_1329_, 0, v___x_1385_);
                    v___x_1391_ = v___x_1329_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1385_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1393_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1392_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
                v___y_1338_ = v___x_1392_;
                state = 5;
                continue;
            }
            10 => {
                if v_isShared_1398_ == 0 {
                    v___x_1400_ = v___x_1397_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1401_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
                    v___x_1400_ = v_reuseFailAlloc_1401_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1400_;
            }
            12 => {
                if v_isShared_1410_ == 0 {
                    v___x_1412_ = v___x_1409_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
                    v___x_1412_ = v_reuseFailAlloc_1413_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1412_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___boxed(
    mut v_e_1417_: *mut leanh::LeanObject,
    mut v_simp_1418_: *mut leanh::LeanObject,
    mut v_a_1419_: *mut leanh::LeanObject,
    mut v_a_1420_: *mut leanh::LeanObject,
    mut v_a_1421_: *mut leanh::LeanObject,
    mut v_a_1422_: *mut leanh::LeanObject,
    mut v_a_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_simp_boxed_1424_: u8 = 0;
    let mut v_res_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_simp_boxed_1424_ = (leanh::lean_unbox(v_simp_1418_) as u8);
    v_res_1425_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(
        v_e_1417_,
        v_simp_boxed_1424_,
        v_a_1419_,
        v_a_1420_,
        v_a_1421_,
        v_a_1422_,
    );
    leanh::lean_dec(v_a_1422_);
    leanh::lean_dec_ref(v_a_1421_);
    leanh::lean_dec(v_a_1420_);
    leanh::lean_dec_ref(v_a_1419_);
    return v_res_1425_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1426_: *mut leanh::LeanObject,
    mut v___y_1427_: *mut leanh::LeanObject,
    mut v___y_1428_: *mut leanh::LeanObject,
    mut v___y_1429_: *mut leanh::LeanObject,
    mut v___y_1430_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = lean_st_ref_get(v___y_1430_);
    v_env_1433_ = leanh::lean_ctor_get(v___x_1432_, 0);
    leanh::lean_inc_ref(v_env_1433_);
    leanh::lean_dec(v___x_1432_);
    v___x_1434_ = lean_st_ref_get(v___y_1428_);
    v_mctx_1435_ = leanh::lean_ctor_get(v___x_1434_, 0);
    leanh::lean_inc_ref(v_mctx_1435_);
    leanh::lean_dec(v___x_1434_);
    v_lctx_1436_ = leanh::lean_ctor_get(v___y_1427_, 2);
    v_options_1437_ = leanh::lean_ctor_get(v___y_1429_, 2);
    leanh::lean_inc_ref(v_options_1437_);
    leanh::lean_inc_ref(v_lctx_1436_);
    v___x_1438_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1438_, 0, v_env_1433_);
    leanh::lean_ctor_set(v___x_1438_, 1, v_mctx_1435_);
    leanh::lean_ctor_set(v___x_1438_, 2, v_lctx_1436_);
    leanh::lean_ctor_set(v___x_1438_, 3, v_options_1437_);
    v___x_1439_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    leanh::lean_ctor_set(v___x_1439_, 1, v_msgData_1426_);
    v___x_1440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1440_, 0, v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
    mut v___y_1444_: *mut leanh::LeanObject,
    mut v___y_1445_: *mut leanh::LeanObject,
    mut v___y_1446_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
    leanh::lean_dec(v___y_1445_);
    leanh::lean_dec_ref(v___y_1444_);
    leanh::lean_dec(v___y_1443_);
    leanh::lean_dec_ref(v___y_1442_);
    return v_res_1447_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(
    mut v_opts_1448_: *mut leanh::LeanObject,
    mut v_opt_1449_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_1450_ = leanh::lean_ctor_get(v_opt_1449_, 0);
    v_defValue_1451_ = leanh::lean_ctor_get(v_opt_1449_, 1);
    v_map_1452_ = leanh::lean_ctor_get(v_opts_1448_, 0);
    v___x_1453_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1452_,
            v_name_1450_,
        );
    if leanh::lean_obj_tag(v___x_1453_) == 0 {
        let mut v___x_1454_: u8 = 0;
        v___x_1454_ = (leanh::lean_unbox(v_defValue_1451_) as u8);
        return v___x_1454_;
    } else {
        let mut v_val_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1455_ = leanh::lean_ctor_get(v___x_1453_, 0);
        leanh::lean_inc(v_val_1455_);
        leanh::lean_dec_ref_known(v___x_1453_, 1);
        if leanh::lean_obj_tag(v_val_1455_) == 1 {
            let mut v_v_1456_: u8 = 0;
            v_v_1456_ = leanh::lean_ctor_get_uint8(v_val_1455_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_1455_, 0);
            return v_v_1456_;
        } else {
            let mut v___x_1457_: u8 = 0;
            leanh::lean_dec(v_val_1455_);
            v___x_1457_ = (leanh::lean_unbox(v_defValue_1451_) as u8);
            return v___x_1457_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_opts_1458_: *mut leanh::LeanObject,
    mut v_opt_1459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1460_: u8 = 0;
    let mut v_r_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_opts_1458_, v_opt_1459_);
    leanh::lean_dec_ref(v_opt_1459_);
    leanh::lean_dec_ref(v_opts_1458_);
    v_r_1461_ = leanh::lean_box((v_res_1460_) as usize);
    return v_r_1461_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = leanh::lean_box(1);
    v___x_1463_ = l_Lean_MessageData_ofFormat(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2;
    v___x_1468_ = l_Lean_MessageData_ofFormat(v___x_1467_);
    return v___x_1468_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(
    mut v_x_1469_: *mut leanh::LeanObject,
    mut v_x_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v_before_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_unused_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1470_) == 0 {
                    return v_x_1469_;
                } else {
                    v_head_1471_ = leanh::lean_ctor_get(v_x_1470_, 0);
                    v_tail_1472_ = leanh::lean_ctor_get(v_x_1470_, 1);
                    v_isSharedCheck_1494_ = (!leanh::lean_is_exclusive(v_x_1470_)) as u8;
                    if v_isSharedCheck_1494_ == 0 {
                        v___x_1474_ = v_x_1470_;
                        v_isShared_1475_ = v_isSharedCheck_1494_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1472_);
                        leanh::lean_inc(v_head_1471_);
                        leanh::lean_dec(v_x_1470_);
                        v___x_1474_ = leanh::lean_box(0);
                        v_isShared_1475_ = v_isSharedCheck_1494_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1476_ = leanh::lean_ctor_get(v_head_1471_, 0);
                v_isSharedCheck_1492_ = (!leanh::lean_is_exclusive(v_head_1471_)) as u8;
                if v_isSharedCheck_1492_ == 0 {
                    v_unused_1493_ = leanh::lean_ctor_get(v_head_1471_, 1);
                    leanh::lean_dec(v_unused_1493_);
                    v___x_1478_ = v_head_1471_;
                    v_isShared_1479_ = v_isSharedCheck_1492_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_1476_);
                    leanh::lean_dec(v_head_1471_);
                    v___x_1478_ = leanh::lean_box(0);
                    v_isShared_1479_ = v_isSharedCheck_1492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1480_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0);
                if v_isShared_1479_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1478_, 7);
                    leanh::lean_ctor_set(v___x_1478_, 1, v___x_1480_);
                    leanh::lean_ctor_set(v___x_1478_, 0, v_x_1469_);
                    v___x_1482_ = v___x_1478_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_x_1469_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1480_);
                    v___x_1482_ = v_reuseFailAlloc_1491_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3);
                if v_isShared_1475_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1474_, 7);
                    leanh::lean_ctor_set(v___x_1474_, 1, v___x_1483_);
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1482_);
                    v___x_1485_ = v___x_1474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1482_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1483_);
                    v___x_1485_ = v_reuseFailAlloc_1490_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1486_ = l_Lean_MessageData_ofSyntax(v_before_1476_);
                v___x_1487_ = l_Lean_indentD(v___x_1486_);
                v___x_1488_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1488_, 0, v___x_1485_);
                leanh::lean_ctor_set(v___x_1488_, 1, v___x_1487_);
                v_x_1469_ = v___x_1488_;
                v_x_1470_ = v_tail_1472_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1;
    v___x_1499_ = l_Lean_MessageData_ofFormat(v___x_1498_);
    return v___x_1499_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(
    mut v_msgData_1500_: *mut leanh::LeanObject,
    mut v_macroStack_1501_: *mut leanh::LeanObject,
    mut v___y_1502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_options_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v_unused_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1504_ = leanh::lean_ctor_get(v___y_1502_, 2);
                v___x_1505_ = l_Lean_Elab_pp_macroStack;
                v___x_1506_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_options_1504_, v___x_1505_);
                if v___x_1506_ == 0 {
                    leanh::lean_dec(v_macroStack_1501_);
                    v___x_1507_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1507_, 0, v_msgData_1500_);
                    return v___x_1507_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_1501_) == 0 {
                        v___x_1508_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1508_, 0, v_msgData_1500_);
                        return v___x_1508_;
                    } else {
                        v_head_1509_ = leanh::lean_ctor_get(v_macroStack_1501_, 0);
                        leanh::lean_inc(v_head_1509_);
                        v_after_1510_ = leanh::lean_ctor_get(v_head_1509_, 1);
                        v_isSharedCheck_1525_ =
                            (!leanh::lean_is_exclusive(v_head_1509_)) as u8;
                        if v_isSharedCheck_1525_ == 0 {
                            v_unused_1526_ = leanh::lean_ctor_get(v_head_1509_, 0);
                            leanh::lean_dec(v_unused_1526_);
                            v___x_1512_ = v_head_1509_;
                            v_isShared_1513_ = v_isSharedCheck_1525_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_1510_);
                            leanh::lean_dec(v_head_1509_);
                            v___x_1512_ = leanh::lean_box(0);
                            v_isShared_1513_ = v_isSharedCheck_1525_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0);
                if v_isShared_1513_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1512_, 7);
                    leanh::lean_ctor_set(v___x_1512_, 1, v___x_1514_);
                    leanh::lean_ctor_set(v___x_1512_, 0, v_msgData_1500_);
                    v___x_1516_ = v___x_1512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_msgData_1500_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1514_);
                    v___x_1516_ = v_reuseFailAlloc_1524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1517_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2);
                v___x_1518_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1518_, 0, v___x_1516_);
                leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                v___x_1519_ = l_Lean_MessageData_ofSyntax(v_after_1510_);
                v___x_1520_ = l_Lean_indentD(v___x_1519_);
                v_msgData_1521_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_1521_, 0, v___x_1518_);
                leanh::lean_ctor_set(v_msgData_1521_, 1, v___x_1520_);
                v___x_1522_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(v_msgData_1521_, v_macroStack_1501_);
                v___x_1523_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1523_, 0, v___x_1522_);
                return v___x_1523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_msgData_1527_: *mut leanh::LeanObject,
    mut v_macroStack_1528_: *mut leanh::LeanObject,
    mut v___y_1529_: *mut leanh::LeanObject,
    mut v___y_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msgData_1527_, v_macroStack_1528_, v___y_1529_);
    leanh::lean_dec_ref(v___y_1529_);
    return v_res_1531_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1532_: *mut leanh::LeanObject,
    mut v___y_1533_: *mut leanh::LeanObject,
    mut v___y_1534_: *mut leanh::LeanObject,
    mut v___y_1535_: *mut leanh::LeanObject,
    mut v___y_1536_: *mut leanh::LeanObject,
    mut v___y_1537_: *mut leanh::LeanObject,
    mut v___y_1538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1540_ = leanh::lean_ctor_get(v___y_1537_, 5);
                v___x_1541_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1532_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
                v_a_1542_ = leanh::lean_ctor_get(v___x_1541_, 0);
                leanh::lean_inc(v_a_1542_);
                leanh::lean_dec_ref(v___x_1541_);
                v_macroStack_1543_ = leanh::lean_ctor_get(v___y_1533_, 1);
                v___x_1544_ = l_Lean_Elab_getBetterRef(v_ref_1540_, v_macroStack_1543_);
                leanh::lean_inc(v_macroStack_1543_);
                v___x_1545_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_a_1542_, v_macroStack_1543_, v___y_1537_);
                v_a_1546_ = leanh::lean_ctor_get(v___x_1545_, 0);
                v_isSharedCheck_1554_ = (!leanh::lean_is_exclusive(v___x_1545_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v___x_1548_ = v___x_1545_;
                    v_isShared_1549_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1546_);
                    leanh::lean_dec(v___x_1545_);
                    v___x_1548_ = leanh::lean_box(0);
                    v_isShared_1549_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1550_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1550_, 0, v___x_1544_);
                leanh::lean_ctor_set(v___x_1550_, 1, v_a_1546_);
                if v_isShared_1549_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1548_, 1);
                    leanh::lean_ctor_set(v___x_1548_, 0, v___x_1550_);
                    v___x_1552_ = v___x_1548_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
                    v___x_1552_ = v_reuseFailAlloc_1553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1552_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg___boxed(
    mut v_msg_1555_: *mut leanh::LeanObject,
    mut v___y_1556_: *mut leanh::LeanObject,
    mut v___y_1557_: *mut leanh::LeanObject,
    mut v___y_1558_: *mut leanh::LeanObject,
    mut v___y_1559_: *mut leanh::LeanObject,
    mut v___y_1560_: *mut leanh::LeanObject,
    mut v___y_1561_: *mut leanh::LeanObject,
    mut v___y_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
    leanh::lean_dec(v___y_1561_);
    leanh::lean_dec_ref(v___y_1560_);
    leanh::lean_dec(v___y_1559_);
    leanh::lean_dec_ref(v___y_1558_);
    leanh::lean_dec(v___y_1557_);
    leanh::lean_dec_ref(v___y_1556_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1564_: *mut leanh::LeanObject,
    mut v_msg_1565_: *mut leanh::LeanObject,
    mut v___y_1566_: *mut leanh::LeanObject,
    mut v___y_1567_: *mut leanh::LeanObject,
    mut v___y_1568_: *mut leanh::LeanObject,
    mut v___y_1569_: *mut leanh::LeanObject,
    mut v___y_1570_: *mut leanh::LeanObject,
    mut v___y_1571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1585_: u8 = 0;
    let mut v_cancelTk_x3f_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1587_: u8 = 0;
    let mut v_inheritedTraceOptions_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1573_ = leanh::lean_ctor_get(v___y_1570_, 0);
    v_fileMap_1574_ = leanh::lean_ctor_get(v___y_1570_, 1);
    v_options_1575_ = leanh::lean_ctor_get(v___y_1570_, 2);
    v_currRecDepth_1576_ = leanh::lean_ctor_get(v___y_1570_, 3);
    v_maxRecDepth_1577_ = leanh::lean_ctor_get(v___y_1570_, 4);
    v_ref_1578_ = leanh::lean_ctor_get(v___y_1570_, 5);
    v_currNamespace_1579_ = leanh::lean_ctor_get(v___y_1570_, 6);
    v_openDecls_1580_ = leanh::lean_ctor_get(v___y_1570_, 7);
    v_initHeartbeats_1581_ = leanh::lean_ctor_get(v___y_1570_, 8);
    v_maxHeartbeats_1582_ = leanh::lean_ctor_get(v___y_1570_, 9);
    v_quotContext_1583_ = leanh::lean_ctor_get(v___y_1570_, 10);
    v_currMacroScope_1584_ = leanh::lean_ctor_get(v___y_1570_, 11);
    v_diag_1585_ = leanh::lean_ctor_get_uint8(
        v___y_1570_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1586_ = leanh::lean_ctor_get(v___y_1570_, 12);
    v_suppressElabErrors_1587_ = leanh::lean_ctor_get_uint8(
        v___y_1570_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1588_ = leanh::lean_ctor_get(v___y_1570_, 13);
    v_ref_1589_ = l_Lean_replaceRef(v_ref_1564_, v_ref_1578_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1588_);
    leanh::lean_inc(v_cancelTk_x3f_1586_);
    leanh::lean_inc(v_currMacroScope_1584_);
    leanh::lean_inc(v_quotContext_1583_);
    leanh::lean_inc(v_maxHeartbeats_1582_);
    leanh::lean_inc(v_initHeartbeats_1581_);
    leanh::lean_inc(v_openDecls_1580_);
    leanh::lean_inc(v_currNamespace_1579_);
    leanh::lean_inc(v_maxRecDepth_1577_);
    leanh::lean_inc(v_currRecDepth_1576_);
    leanh::lean_inc_ref(v_options_1575_);
    leanh::lean_inc_ref(v_fileMap_1574_);
    leanh::lean_inc_ref(v_fileName_1573_);
    v___x_1590_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1590_, 0, v_fileName_1573_);
    leanh::lean_ctor_set(v___x_1590_, 1, v_fileMap_1574_);
    leanh::lean_ctor_set(v___x_1590_, 2, v_options_1575_);
    leanh::lean_ctor_set(v___x_1590_, 3, v_currRecDepth_1576_);
    leanh::lean_ctor_set(v___x_1590_, 4, v_maxRecDepth_1577_);
    leanh::lean_ctor_set(v___x_1590_, 5, v_ref_1589_);
    leanh::lean_ctor_set(v___x_1590_, 6, v_currNamespace_1579_);
    leanh::lean_ctor_set(v___x_1590_, 7, v_openDecls_1580_);
    leanh::lean_ctor_set(v___x_1590_, 8, v_initHeartbeats_1581_);
    leanh::lean_ctor_set(v___x_1590_, 9, v_maxHeartbeats_1582_);
    leanh::lean_ctor_set(v___x_1590_, 10, v_quotContext_1583_);
    leanh::lean_ctor_set(v___x_1590_, 11, v_currMacroScope_1584_);
    leanh::lean_ctor_set(v___x_1590_, 12, v_cancelTk_x3f_1586_);
    leanh::lean_ctor_set(v___x_1590_, 13, v_inheritedTraceOptions_1588_);
    leanh::lean_ctor_set_uint8(
        v___x_1590_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1585_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1590_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1587_,
    );
    v___x_1591_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___x_1590_, v___y_1571_);
    leanh::lean_dec_ref_known(v___x_1590_, 14);
    return v___x_1591_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1592_: *mut leanh::LeanObject,
    mut v_msg_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
    mut v___y_1596_: *mut leanh::LeanObject,
    mut v___y_1597_: *mut leanh::LeanObject,
    mut v___y_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1592_, v_msg_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
    leanh::lean_dec(v___y_1599_);
    leanh::lean_dec_ref(v___y_1598_);
    leanh::lean_dec(v___y_1597_);
    leanh::lean_dec_ref(v___y_1596_);
    leanh::lean_dec(v___y_1595_);
    leanh::lean_dec_ref(v___y_1594_);
    leanh::lean_dec(v_ref_1592_);
    return v_res_1601_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_1604_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1604_, 0, v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1606_ = leanh::lean_unsigned_to_nat(0);
    v___x_1607_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1607_, 0, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 3, v___x_1606_);
    leanh::lean_ctor_set(v___x_1607_, 4, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 5, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 6, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 7, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 8, v___x_1605_);
    leanh::lean_ctor_set(v___x_1607_, 9, v___x_1605_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = leanh::lean_unsigned_to_nat(32);
    v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1608_);
    v___x_1610_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1611_: usize = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = 5usize;
    v___x_1612_ = leanh::lean_unsigned_to_nat(0);
    v___x_1613_ = leanh::lean_unsigned_to_nat(32);
    v___x_1614_ = lean_mk_empty_array_with_capacity(v___x_1613_);
    v___x_1615_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_1616_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1616_, 0, v___x_1615_);
    leanh::lean_ctor_set(v___x_1616_, 1, v___x_1614_);
    leanh::lean_ctor_set(v___x_1616_, 2, v___x_1612_);
    leanh::lean_ctor_set(v___x_1616_, 3, v___x_1612_);
    leanh::lean_ctor_set_usize(v___x_1616_, 4, v___x_1611_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = leanh::lean_box(1);
    v___x_1618_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1619_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1620_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1620_, 0, v___x_1619_);
    leanh::lean_ctor_set(v___x_1620_, 1, v___x_1618_);
    leanh::lean_ctor_set(v___x_1620_, 2, v___x_1617_);
    return v___x_1620_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
    return v___x_1629_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
    return v___x_1635_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1642_: *mut leanh::LeanObject,
    mut v_declHint_1643_: *mut leanh::LeanObject,
    mut v___y_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v_isExporting_1649_: u8 = 0;
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1646_ = lean_st_ref_get(v___y_1644_);
                v_env_1647_ = leanh::lean_ctor_get(v___x_1646_, 0);
                leanh::lean_inc_ref(v_env_1647_);
                leanh::lean_dec(v___x_1646_);
                v___x_1648_ = l_Lean_Name_isAnonymous(v_declHint_1643_);
                if v___x_1648_ == 0 {
                    v_isExporting_1649_ = leanh::lean_ctor_get_uint8(
                        v_env_1647_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1649_ == 0 {
                        leanh::lean_dec_ref(v_env_1647_);
                        leanh::lean_dec(v_declHint_1643_);
                        v___x_1650_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1650_, 0, v_msg_1642_);
                        return v___x_1650_;
                    } else {
                        leanh::lean_inc_ref(v_env_1647_);
                        v___x_1651_ = l_Lean_Environment_setExporting(v_env_1647_, v___x_1648_);
                        leanh::lean_inc(v_declHint_1643_);
                        leanh::lean_inc_ref(v___x_1651_);
                        v___x_1652_ = l_Lean_Environment_contains(
                            v___x_1651_,
                            v_declHint_1643_,
                            v_isExporting_1649_,
                        );
                        if v___x_1652_ == 0 {
                            leanh::lean_dec_ref(v___x_1651_);
                            leanh::lean_dec_ref(v_env_1647_);
                            leanh::lean_dec(v_declHint_1643_);
                            v___x_1653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1653_, 0, v_msg_1642_);
                            return v___x_1653_;
                        } else {
                            v___x_1654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1655_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1656_ = l_Lean_Options_empty;
                            v___x_1657_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1657_, 0, v___x_1651_);
                            leanh::lean_ctor_set(v___x_1657_, 1, v___x_1654_);
                            leanh::lean_ctor_set(v___x_1657_, 2, v___x_1655_);
                            leanh::lean_ctor_set(v___x_1657_, 3, v___x_1656_);
                            leanh::lean_inc(v_declHint_1643_);
                            v___x_1658_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1643_, v___x_1648_);
                            v_c_1659_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1659_, 0, v___x_1657_);
                            leanh::lean_ctor_set(v_c_1659_, 1, v___x_1658_);
                            v___x_1660_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1647_,
                                v_declHint_1643_,
                            );
                            if leanh::lean_obj_tag(v___x_1660_) == 0 {
                                leanh::lean_dec_ref(v_env_1647_);
                                leanh::lean_dec(v_declHint_1643_);
                                v___x_1661_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1662_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
                                leanh::lean_ctor_set(v___x_1662_, 1, v_c_1659_);
                                v___x_1663_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1664_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1664_, 0, v___x_1662_);
                                leanh::lean_ctor_set(v___x_1664_, 1, v___x_1663_);
                                v___x_1665_ = l_Lean_MessageData_note(v___x_1664_);
                                v___x_1666_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1666_, 0, v_msg_1642_);
                                leanh::lean_ctor_set(v___x_1666_, 1, v___x_1665_);
                                v___x_1667_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
                                return v___x_1667_;
                            } else {
                                v_val_1668_ = leanh::lean_ctor_get(v___x_1660_, 0);
                                v_isSharedCheck_1703_ =
                                    (!leanh::lean_is_exclusive(v___x_1660_)) as u8;
                                if v_isSharedCheck_1703_ == 0 {
                                    v___x_1670_ = v___x_1660_;
                                    v_isShared_1671_ = v_isSharedCheck_1703_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1668_);
                                    leanh::lean_dec(v___x_1660_);
                                    v___x_1670_ = leanh::lean_box(0);
                                    v_isShared_1671_ = v_isSharedCheck_1703_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1647_);
                    leanh::lean_dec(v_declHint_1643_);
                    v___x_1704_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1704_, 0, v_msg_1642_);
                    return v___x_1704_;
                }
            }
            1 => {
                v___x_1672_ = leanh::lean_box(0);
                v___x_1673_ = l_Lean_Environment_header(v_env_1647_);
                leanh::lean_dec_ref(v_env_1647_);
                v___x_1674_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1673_);
                v_mod_1675_ = lean_array_get(v___x_1672_, v___x_1674_, v_val_1668_);
                leanh::lean_dec(v_val_1668_);
                leanh::lean_dec_ref(v___x_1674_);
                v___x_1676_ = l_Lean_isPrivateName(v_declHint_1643_);
                leanh::lean_dec(v_declHint_1643_);
                if v___x_1676_ == 0 {
                    v___x_1677_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1678_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                    leanh::lean_ctor_set(v___x_1678_, 1, v_c_1659_);
                    v___x_1679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1680_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1680_, 0, v___x_1678_);
                    leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
                    v___x_1681_ = l_Lean_MessageData_ofName(v_mod_1675_);
                    v___x_1682_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1682_, 0, v___x_1680_);
                    leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                    v___x_1683_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1684_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1684_, 0, v___x_1682_);
                    leanh::lean_ctor_set(v___x_1684_, 1, v___x_1683_);
                    v___x_1685_ = l_Lean_MessageData_note(v___x_1684_);
                    v___x_1686_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1686_, 0, v_msg_1642_);
                    leanh::lean_ctor_set(v___x_1686_, 1, v___x_1685_);
                    if v_isShared_1671_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1670_, 0);
                        leanh::lean_ctor_set(v___x_1670_, 0, v___x_1686_);
                        v___x_1688_ = v___x_1670_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
                        v___x_1688_ = v_reuseFailAlloc_1689_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1690_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1691_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1691_, 0, v___x_1690_);
                    leanh::lean_ctor_set(v___x_1691_, 1, v_c_1659_);
                    v___x_1692_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1693_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1693_, 0, v___x_1691_);
                    leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                    v___x_1694_ = l_Lean_MessageData_ofName(v_mod_1675_);
                    v___x_1695_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1695_, 0, v___x_1693_);
                    leanh::lean_ctor_set(v___x_1695_, 1, v___x_1694_);
                    v___x_1696_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1697_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1697_, 0, v___x_1695_);
                    leanh::lean_ctor_set(v___x_1697_, 1, v___x_1696_);
                    v___x_1698_ = l_Lean_MessageData_note(v___x_1697_);
                    v___x_1699_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1699_, 0, v_msg_1642_);
                    leanh::lean_ctor_set(v___x_1699_, 1, v___x_1698_);
                    if v_isShared_1671_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1670_, 0);
                        leanh::lean_ctor_set(v___x_1670_, 0, v___x_1699_);
                        v___x_1701_ = v___x_1670_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1702_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
                        v___x_1701_ = v_reuseFailAlloc_1702_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1688_;
            }
            3 => {
                return v___x_1701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_msg_1705_: *mut leanh::LeanObject,
    mut v_declHint_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1705_, v_declHint_1706_, v___y_1707_);
    leanh::lean_dec(v___y_1707_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1710_: *mut leanh::LeanObject,
    mut v_declHint_1711_: *mut leanh::LeanObject,
    mut v___y_1712_: *mut leanh::LeanObject,
    mut v___y_1713_: *mut leanh::LeanObject,
    mut v___y_1714_: *mut leanh::LeanObject,
    mut v___y_1715_: *mut leanh::LeanObject,
    mut v___y_1716_: *mut leanh::LeanObject,
    mut v___y_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1710_, v_declHint_1711_, v___y_1717_);
                v_a_1720_ = leanh::lean_ctor_get(v___x_1719_, 0);
                v_isSharedCheck_1729_ = (!leanh::lean_is_exclusive(v___x_1719_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v___x_1722_ = v___x_1719_;
                    v_isShared_1723_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1720_);
                    leanh::lean_dec(v___x_1719_);
                    v___x_1722_ = leanh::lean_box(0);
                    v_isShared_1723_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1724_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1725_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                leanh::lean_ctor_set(v___x_1725_, 1, v_a_1720_);
                if v_isShared_1723_ == 0 {
                    leanh::lean_ctor_set(v___x_1722_, 0, v___x_1725_);
                    v___x_1727_ = v___x_1722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
                    v___x_1727_ = v_reuseFailAlloc_1728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3___boxed(
    mut v_msg_1730_: *mut leanh::LeanObject,
    mut v_declHint_1731_: *mut leanh::LeanObject,
    mut v___y_1732_: *mut leanh::LeanObject,
    mut v___y_1733_: *mut leanh::LeanObject,
    mut v___y_1734_: *mut leanh::LeanObject,
    mut v___y_1735_: *mut leanh::LeanObject,
    mut v___y_1736_: *mut leanh::LeanObject,
    mut v___y_1737_: *mut leanh::LeanObject,
    mut v___y_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1730_, v_declHint_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
    leanh::lean_dec(v___y_1737_);
    leanh::lean_dec_ref(v___y_1736_);
    leanh::lean_dec(v___y_1735_);
    leanh::lean_dec_ref(v___y_1734_);
    leanh::lean_dec(v___y_1733_);
    leanh::lean_dec_ref(v___y_1732_);
    return v_res_1739_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1740_: *mut leanh::LeanObject,
    mut v_msg_1741_: *mut leanh::LeanObject,
    mut v_declHint_1742_: *mut leanh::LeanObject,
    mut v___y_1743_: *mut leanh::LeanObject,
    mut v___y_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
    mut v___y_1747_: *mut leanh::LeanObject,
    mut v___y_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1741_, v_declHint_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
    v_a_1751_ = leanh::lean_ctor_get(v___x_1750_, 0);
    leanh::lean_inc(v_a_1751_);
    leanh::lean_dec_ref(v___x_1750_);
    v___x_1752_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1740_, v_a_1751_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1753_: *mut leanh::LeanObject,
    mut v_msg_1754_: *mut leanh::LeanObject,
    mut v_declHint_1755_: *mut leanh::LeanObject,
    mut v___y_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
    mut v___y_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
    mut v___y_1762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1753_, v_msg_1754_, v_declHint_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
    leanh::lean_dec(v___y_1761_);
    leanh::lean_dec_ref(v___y_1760_);
    leanh::lean_dec(v___y_1759_);
    leanh::lean_dec_ref(v___y_1758_);
    leanh::lean_dec(v___y_1757_);
    leanh::lean_dec_ref(v___y_1756_);
    leanh::lean_dec(v_ref_1753_);
    return v_res_1763_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1770_: *mut leanh::LeanObject,
    mut v_constName_1771_: *mut leanh::LeanObject,
    mut v___y_1772_: *mut leanh::LeanObject,
    mut v___y_1773_: *mut leanh::LeanObject,
    mut v___y_1774_: *mut leanh::LeanObject,
    mut v___y_1775_: *mut leanh::LeanObject,
    mut v___y_1776_: *mut leanh::LeanObject,
    mut v___y_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1780_ = 0;
    leanh::lean_inc(v_constName_1771_);
    v___x_1781_ = l_Lean_MessageData_ofConstName(v_constName_1771_, v___x_1780_);
    v___x_1782_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1782_, 0, v___x_1779_);
    leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
    v___x_1783_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1784_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1784_, 0, v___x_1782_);
    leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
    v___x_1785_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1770_, v___x_1784_, v_constName_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
    return v___x_1785_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1786_: *mut leanh::LeanObject,
    mut v_constName_1787_: *mut leanh::LeanObject,
    mut v___y_1788_: *mut leanh::LeanObject,
    mut v___y_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(v_ref_1786_, v_constName_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
    leanh::lean_dec(v___y_1793_);
    leanh::lean_dec_ref(v___y_1792_);
    leanh::lean_dec(v___y_1791_);
    leanh::lean_dec_ref(v___y_1790_);
    leanh::lean_dec(v___y_1789_);
    leanh::lean_dec_ref(v___y_1788_);
    leanh::lean_dec(v_ref_1786_);
    return v_res_1795_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(
    mut v_constName_1796_: *mut leanh::LeanObject,
    mut v___y_1797_: *mut leanh::LeanObject,
    mut v___y_1798_: *mut leanh::LeanObject,
    mut v___y_1799_: *mut leanh::LeanObject,
    mut v___y_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1804_ = leanh::lean_ctor_get(v___y_1801_, 5);
    v___x_1805_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(v_ref_1804_, v_constName_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1806_: *mut leanh::LeanObject,
    mut v___y_1807_: *mut leanh::LeanObject,
    mut v___y_1808_: *mut leanh::LeanObject,
    mut v___y_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
    mut v___y_1813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(v_constName_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
    leanh::lean_dec(v___y_1812_);
    leanh::lean_dec_ref(v___y_1811_);
    leanh::lean_dec(v___y_1810_);
    leanh::lean_dec_ref(v___y_1809_);
    leanh::lean_dec(v___y_1808_);
    leanh::lean_dec_ref(v___y_1807_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(
    mut v_constName_1815_: *mut leanh::LeanObject,
    mut v___y_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
    mut v___y_1819_: *mut leanh::LeanObject,
    mut v___y_1820_: *mut leanh::LeanObject,
    mut v___y_1821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1823_ = lean_st_ref_get(v___y_1821_);
                v_env_1824_ = leanh::lean_ctor_get(v___x_1823_, 0);
                leanh::lean_inc_ref(v_env_1824_);
                leanh::lean_dec(v___x_1823_);
                v___x_1825_ = 0;
                leanh::lean_inc(v_constName_1815_);
                v___x_1826_ =
                    l_Lean_Environment_find_x3f(v_env_1824_, v_constName_1815_, v___x_1825_);
                if leanh::lean_obj_tag(v___x_1826_) == 0 {
                    v___x_1827_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(v_constName_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
                    return v___x_1827_;
                } else {
                    leanh::lean_dec(v_constName_1815_);
                    v_val_1828_ = leanh::lean_ctor_get(v___x_1826_, 0);
                    v_isSharedCheck_1835_ = (!leanh::lean_is_exclusive(v___x_1826_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1830_ = v___x_1826_;
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1828_);
                        leanh::lean_dec(v___x_1826_);
                        v___x_1830_ = leanh::lean_box(0);
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1831_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1830_, 0);
                    v___x_1833_ = v___x_1830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_val_1828_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0___boxed(
    mut v_constName_1836_: *mut leanh::LeanObject,
    mut v___y_1837_: *mut leanh::LeanObject,
    mut v___y_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
    mut v___y_1843_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(v_constName_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
    leanh::lean_dec(v___y_1842_);
    leanh::lean_dec_ref(v___y_1841_);
    leanh::lean_dec(v___y_1840_);
    leanh::lean_dec_ref(v___y_1839_);
    leanh::lean_dec(v___y_1838_);
    leanh::lean_dec_ref(v___y_1837_);
    return v_res_1844_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(
    mut v_t_1848_: *mut leanh::LeanObject,
    mut v_a_1849_: *mut leanh::LeanObject,
    mut v_a_1850_: *mut leanh::LeanObject,
    mut v_a_1851_: *mut leanh::LeanObject,
    mut v_a_1852_: *mut leanh::LeanObject,
    mut v_a_1853_: *mut leanh::LeanObject,
    mut v_a_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_a_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_a_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1856_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1;
                leanh::lean_inc(v_t_1848_);
                v___x_1857_ = l_Lean_Syntax_isOfKind(v_t_1848_, v___x_1856_);
                if v___x_1857_ == 0 {
                    v___x_1858_ = leanh::lean_box(0);
                    v___x_1859_ = 1;
                    v___x_1860_ = l_Lean_Elab_Term_elabTerm(
                        v_t_1848_,
                        v___x_1858_,
                        v___x_1859_,
                        v___x_1859_,
                        v_a_1849_,
                        v_a_1850_,
                        v_a_1851_,
                        v_a_1852_,
                        v_a_1853_,
                        v_a_1854_,
                    );
                    return v___x_1860_;
                } else {
                    v_lctx_1861_ = leanh::lean_ctor_get(v_a_1851_, 2);
                    v___x_1862_ = l_Lean_TSyntax_getId(v_t_1848_);
                    v___x_1863_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1861_, v___x_1862_);
                    leanh::lean_dec(v___x_1862_);
                    if leanh::lean_obj_tag(v___x_1863_) == 1 {
                        leanh::lean_dec(v_t_1848_);
                        v_val_1864_ = leanh::lean_ctor_get(v___x_1863_, 0);
                        v_isSharedCheck_1872_ =
                            (!leanh::lean_is_exclusive(v___x_1863_)) as u8;
                        if v_isSharedCheck_1872_ == 0 {
                            v___x_1866_ = v___x_1863_;
                            v_isShared_1867_ = v_isSharedCheck_1872_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1864_);
                            leanh::lean_dec(v___x_1863_);
                            v___x_1866_ = leanh::lean_box(0);
                            v_isShared_1867_ = v_isSharedCheck_1872_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_1863_);
                        v___x_1873_ = leanh::lean_box(0);
                        v___x_1874_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                            v_t_1848_,
                            v___x_1873_,
                            v_a_1853_,
                            v_a_1854_,
                        );
                        if leanh::lean_obj_tag(v___x_1874_) == 0 {
                            v_a_1875_ = leanh::lean_ctor_get(v___x_1874_, 0);
                            leanh::lean_inc(v_a_1875_);
                            leanh::lean_dec_ref_known(v___x_1874_, 1);
                            v___x_1876_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(v_a_1875_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
                            if leanh::lean_obj_tag(v___x_1876_) == 0 {
                                v_a_1877_ = leanh::lean_ctor_get(v___x_1876_, 0);
                                v_isSharedCheck_1885_ =
                                    (!leanh::lean_is_exclusive(v___x_1876_)) as u8;
                                if v_isSharedCheck_1885_ == 0 {
                                    v___x_1879_ = v___x_1876_;
                                    v_isShared_1880_ = v_isSharedCheck_1885_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1877_);
                                    leanh::lean_dec(v___x_1876_);
                                    v___x_1879_ = leanh::lean_box(0);
                                    v_isShared_1880_ = v_isSharedCheck_1885_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_1886_ = leanh::lean_ctor_get(v___x_1876_, 0);
                                v_isSharedCheck_1893_ =
                                    (!leanh::lean_is_exclusive(v___x_1876_)) as u8;
                                if v_isSharedCheck_1893_ == 0 {
                                    v___x_1888_ = v___x_1876_;
                                    v_isShared_1889_ = v_isSharedCheck_1893_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_1886_);
                                    leanh::lean_dec(v___x_1876_);
                                    v___x_1888_ = leanh::lean_box(0);
                                    v_isShared_1889_ = v_isSharedCheck_1893_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1894_ = leanh::lean_ctor_get(v___x_1874_, 0);
                            v_isSharedCheck_1901_ =
                                (!leanh::lean_is_exclusive(v___x_1874_)) as u8;
                            if v_isSharedCheck_1901_ == 0 {
                                v___x_1896_ = v___x_1874_;
                                v_isShared_1897_ = v_isSharedCheck_1901_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1894_);
                                leanh::lean_dec(v___x_1874_);
                                v___x_1896_ = leanh::lean_box(0);
                                v_isShared_1897_ = v_isSharedCheck_1901_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1868_ = l_Lean_LocalDecl_type(v_val_1864_);
                leanh::lean_dec(v_val_1864_);
                if v_isShared_1867_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1866_, 0);
                    leanh::lean_ctor_set(v___x_1866_, 0, v___x_1868_);
                    v___x_1870_ = v___x_1866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
                    v___x_1870_ = v_reuseFailAlloc_1871_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1870_;
            }
            3 => {
                v___x_1881_ = l_Lean_ConstantInfo_type(v_a_1877_);
                leanh::lean_dec(v_a_1877_);
                if v_isShared_1880_ == 0 {
                    leanh::lean_ctor_set(v___x_1879_, 0, v___x_1881_);
                    v___x_1883_ = v___x_1879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1883_;
            }
            5 => {
                if v_isShared_1889_ == 0 {
                    v___x_1891_ = v___x_1888_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1891_;
            }
            7 => {
                if v_isShared_1897_ == 0 {
                    v___x_1899_ = v___x_1896_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1900_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
                    v___x_1899_ = v_reuseFailAlloc_1900_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___boxed(
    mut v_t_1902_: *mut leanh::LeanObject,
    mut v_a_1903_: *mut leanh::LeanObject,
    mut v_a_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
    mut v_a_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
    mut v_a_1909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ =
        l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(
            v_t_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_,
        );
    leanh::lean_dec(v_a_1908_);
    leanh::lean_dec_ref(v_a_1907_);
    leanh::lean_dec(v_a_1906_);
    leanh::lean_dec_ref(v_a_1905_);
    leanh::lean_dec(v_a_1904_);
    leanh::lean_dec_ref(v_a_1903_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0(
    mut v_00_u03b1_1911_: *mut leanh::LeanObject,
    mut v_constName_1912_: *mut leanh::LeanObject,
    mut v___y_1913_: *mut leanh::LeanObject,
    mut v___y_1914_: *mut leanh::LeanObject,
    mut v___y_1915_: *mut leanh::LeanObject,
    mut v___y_1916_: *mut leanh::LeanObject,
    mut v___y_1917_: *mut leanh::LeanObject,
    mut v___y_1918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(v_constName_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1921_: *mut leanh::LeanObject,
    mut v_constName_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
    mut v___y_1928_: *mut leanh::LeanObject,
    mut v___y_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0(v_00_u03b1_1921_, v_constName_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
    leanh::lean_dec(v___y_1928_);
    leanh::lean_dec_ref(v___y_1927_);
    leanh::lean_dec(v___y_1926_);
    leanh::lean_dec_ref(v___y_1925_);
    leanh::lean_dec(v___y_1924_);
    leanh::lean_dec_ref(v___y_1923_);
    return v_res_1930_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1931_: *mut leanh::LeanObject,
    mut v_ref_1932_: *mut leanh::LeanObject,
    mut v_constName_1933_: *mut leanh::LeanObject,
    mut v___y_1934_: *mut leanh::LeanObject,
    mut v___y_1935_: *mut leanh::LeanObject,
    mut v___y_1936_: *mut leanh::LeanObject,
    mut v___y_1937_: *mut leanh::LeanObject,
    mut v___y_1938_: *mut leanh::LeanObject,
    mut v___y_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(v_ref_1932_, v_constName_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
    return v___x_1941_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1942_: *mut leanh::LeanObject,
    mut v_ref_1943_: *mut leanh::LeanObject,
    mut v_constName_1944_: *mut leanh::LeanObject,
    mut v___y_1945_: *mut leanh::LeanObject,
    mut v___y_1946_: *mut leanh::LeanObject,
    mut v___y_1947_: *mut leanh::LeanObject,
    mut v___y_1948_: *mut leanh::LeanObject,
    mut v___y_1949_: *mut leanh::LeanObject,
    mut v___y_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1(v_00_u03b1_1942_, v_ref_1943_, v_constName_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
    leanh::lean_dec(v___y_1950_);
    leanh::lean_dec_ref(v___y_1949_);
    leanh::lean_dec(v___y_1948_);
    leanh::lean_dec_ref(v___y_1947_);
    leanh::lean_dec(v___y_1946_);
    leanh::lean_dec_ref(v___y_1945_);
    leanh::lean_dec(v_ref_1943_);
    return v_res_1952_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_1953_: *mut leanh::LeanObject,
    mut v_ref_1954_: *mut leanh::LeanObject,
    mut v_msg_1955_: *mut leanh::LeanObject,
    mut v_declHint_1956_: *mut leanh::LeanObject,
    mut v___y_1957_: *mut leanh::LeanObject,
    mut v___y_1958_: *mut leanh::LeanObject,
    mut v___y_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1954_, v_msg_1955_, v_declHint_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
    return v___x_1964_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_1965_: *mut leanh::LeanObject,
    mut v_ref_1966_: *mut leanh::LeanObject,
    mut v_msg_1967_: *mut leanh::LeanObject,
    mut v_declHint_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
    mut v___y_1970_: *mut leanh::LeanObject,
    mut v___y_1971_: *mut leanh::LeanObject,
    mut v___y_1972_: *mut leanh::LeanObject,
    mut v___y_1973_: *mut leanh::LeanObject,
    mut v___y_1974_: *mut leanh::LeanObject,
    mut v___y_1975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1965_, v_ref_1966_, v_msg_1967_, v_declHint_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
    leanh::lean_dec(v___y_1974_);
    leanh::lean_dec_ref(v___y_1973_);
    leanh::lean_dec(v___y_1972_);
    leanh::lean_dec_ref(v___y_1971_);
    leanh::lean_dec(v___y_1970_);
    leanh::lean_dec_ref(v___y_1969_);
    leanh::lean_dec(v_ref_1966_);
    return v_res_1976_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_1977_: *mut leanh::LeanObject,
    mut v_declHint_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
    mut v___y_1981_: *mut leanh::LeanObject,
    mut v___y_1982_: *mut leanh::LeanObject,
    mut v___y_1983_: *mut leanh::LeanObject,
    mut v___y_1984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1977_, v_declHint_1978_, v___y_1984_);
    return v___x_1986_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1987_: *mut leanh::LeanObject,
    mut v_declHint_1988_: *mut leanh::LeanObject,
    mut v___y_1989_: *mut leanh::LeanObject,
    mut v___y_1990_: *mut leanh::LeanObject,
    mut v___y_1991_: *mut leanh::LeanObject,
    mut v___y_1992_: *mut leanh::LeanObject,
    mut v___y_1993_: *mut leanh::LeanObject,
    mut v___y_1994_: *mut leanh::LeanObject,
    mut v___y_1995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1996_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1987_, v_declHint_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
    leanh::lean_dec(v___y_1994_);
    leanh::lean_dec_ref(v___y_1993_);
    leanh::lean_dec(v___y_1992_);
    leanh::lean_dec_ref(v___y_1991_);
    leanh::lean_dec(v___y_1990_);
    leanh::lean_dec_ref(v___y_1989_);
    return v_res_1996_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_1997_: *mut leanh::LeanObject,
    mut v_ref_1998_: *mut leanh::LeanObject,
    mut v_msg_1999_: *mut leanh::LeanObject,
    mut v___y_2000_: *mut leanh::LeanObject,
    mut v___y_2001_: *mut leanh::LeanObject,
    mut v___y_2002_: *mut leanh::LeanObject,
    mut v___y_2003_: *mut leanh::LeanObject,
    mut v___y_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1998_, v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
    return v___x_2007_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_2008_: *mut leanh::LeanObject,
    mut v_ref_2009_: *mut leanh::LeanObject,
    mut v_msg_2010_: *mut leanh::LeanObject,
    mut v___y_2011_: *mut leanh::LeanObject,
    mut v___y_2012_: *mut leanh::LeanObject,
    mut v___y_2013_: *mut leanh::LeanObject,
    mut v___y_2014_: *mut leanh::LeanObject,
    mut v___y_2015_: *mut leanh::LeanObject,
    mut v___y_2016_: *mut leanh::LeanObject,
    mut v___y_2017_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2008_, v_ref_2009_, v_msg_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
    leanh::lean_dec(v___y_2016_);
    leanh::lean_dec_ref(v___y_2015_);
    leanh::lean_dec(v___y_2014_);
    leanh::lean_dec_ref(v___y_2013_);
    leanh::lean_dec(v___y_2012_);
    leanh::lean_dec_ref(v___y_2011_);
    leanh::lean_dec(v_ref_2009_);
    return v_res_2018_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_2019_: *mut leanh::LeanObject,
    mut v_msg_2020_: *mut leanh::LeanObject,
    mut v___y_2021_: *mut leanh::LeanObject,
    mut v___y_2022_: *mut leanh::LeanObject,
    mut v___y_2023_: *mut leanh::LeanObject,
    mut v___y_2024_: *mut leanh::LeanObject,
    mut v___y_2025_: *mut leanh::LeanObject,
    mut v___y_2026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
    return v___x_2028_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2029_: *mut leanh::LeanObject,
    mut v_msg_2030_: *mut leanh::LeanObject,
    mut v___y_2031_: *mut leanh::LeanObject,
    mut v___y_2032_: *mut leanh::LeanObject,
    mut v___y_2033_: *mut leanh::LeanObject,
    mut v___y_2034_: *mut leanh::LeanObject,
    mut v___y_2035_: *mut leanh::LeanObject,
    mut v___y_2036_: *mut leanh::LeanObject,
    mut v___y_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2029_, v_msg_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
    leanh::lean_dec(v___y_2036_);
    leanh::lean_dec_ref(v___y_2035_);
    leanh::lean_dec(v___y_2034_);
    leanh::lean_dec_ref(v___y_2033_);
    leanh::lean_dec(v___y_2032_);
    leanh::lean_dec_ref(v___y_2031_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(
    mut v_msgData_2039_: *mut leanh::LeanObject,
    mut v_macroStack_2040_: *mut leanh::LeanObject,
    mut v___y_2041_: *mut leanh::LeanObject,
    mut v___y_2042_: *mut leanh::LeanObject,
    mut v___y_2043_: *mut leanh::LeanObject,
    mut v___y_2044_: *mut leanh::LeanObject,
    mut v___y_2045_: *mut leanh::LeanObject,
    mut v___y_2046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msgData_2039_, v_macroStack_2040_, v___y_2045_);
    return v___x_2048_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(
    mut v_msgData_2049_: *mut leanh::LeanObject,
    mut v_macroStack_2050_: *mut leanh::LeanObject,
    mut v___y_2051_: *mut leanh::LeanObject,
    mut v___y_2052_: *mut leanh::LeanObject,
    mut v___y_2053_: *mut leanh::LeanObject,
    mut v___y_2054_: *mut leanh::LeanObject,
    mut v___y_2055_: *mut leanh::LeanObject,
    mut v___y_2056_: *mut leanh::LeanObject,
    mut v___y_2057_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2058_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_msgData_2049_, v_macroStack_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
    leanh::lean_dec(v___y_2056_);
    leanh::lean_dec_ref(v___y_2055_);
    leanh::lean_dec(v___y_2054_);
    leanh::lean_dec_ref(v___y_2053_);
    leanh::lean_dec(v___y_2052_);
    leanh::lean_dec_ref(v___y_2051_);
    return v_res_2058_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = leanh::lean_box(0);
    v___x_2060_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2061_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2061_, 0, v___x_2060_);
    leanh::lean_ctor_set(v___x_2061_, 1, v___x_2059_);
    return v___x_2061_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0);
    v___x_2064_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    return v___x_2064_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___boxed(
    mut v___y_2065_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
    return v_res_2066_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(
    mut v_00_u03b1_2067_: *mut leanh::LeanObject,
    mut v___y_2068_: *mut leanh::LeanObject,
    mut v___y_2069_: *mut leanh::LeanObject,
    mut v___y_2070_: *mut leanh::LeanObject,
    mut v___y_2071_: *mut leanh::LeanObject,
    mut v___y_2072_: *mut leanh::LeanObject,
    mut v___y_2073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
    return v___x_2075_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___boxed(
    mut v_00_u03b1_2076_: *mut leanh::LeanObject,
    mut v___y_2077_: *mut leanh::LeanObject,
    mut v___y_2078_: *mut leanh::LeanObject,
    mut v___y_2079_: *mut leanh::LeanObject,
    mut v___y_2080_: *mut leanh::LeanObject,
    mut v___y_2081_: *mut leanh::LeanObject,
    mut v___y_2082_: *mut leanh::LeanObject,
    mut v___y_2083_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(v_00_u03b1_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
    leanh::lean_dec(v___y_2082_);
    leanh::lean_dec_ref(v___y_2081_);
    leanh::lean_dec(v___y_2080_);
    leanh::lean_dec_ref(v___y_2079_);
    leanh::lean_dec(v___y_2078_);
    leanh::lean_dec_ref(v___y_2077_);
    return v_res_2084_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0(
    mut v___y_2093_: u8,
    mut v_suppressElabErrors_2094_: u8,
    mut v_x_2095_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2095_) == 1 {
        let mut v_pre_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_pre_2096_ = leanh::lean_ctor_get(v_x_2095_, 0);
        match leanh::lean_obj_tag(v_pre_2096_) {
            1 => {
                let mut v_pre_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_pre_2097_ = leanh::lean_ctor_get(v_pre_2096_, 0);
                match leanh::lean_obj_tag(v_pre_2097_) {
                    0 => {
                        let mut v_str_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2101_: u8 = 0;
                        v_str_2098_ = leanh::lean_ctor_get(v_x_2095_, 1);
                        v_str_2099_ = leanh::lean_ctor_get(v_pre_2096_, 1);
                        v___x_2100_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0;
                        v___x_2101_ = lean_string_dec_eq(v_str_2099_, v___x_2100_);
                        if v___x_2101_ == 0 {
                            let mut v___x_2102_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2103_: u8 = 0;
                            v___x_2102_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1;
                            v___x_2103_ = lean_string_dec_eq(v_str_2099_, v___x_2102_);
                            if v___x_2103_ == 0 {
                                return v___y_2093_;
                            } else {
                                let mut v___x_2104_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2105_: u8 = 0;
                                v___x_2104_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2;
                                v___x_2105_ = lean_string_dec_eq(v_str_2098_, v___x_2104_);
                                if v___x_2105_ == 0 {
                                    return v___y_2093_;
                                } else {
                                    return v_suppressElabErrors_2094_;
                                }
                            }
                        } else {
                            let mut v___x_2106_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2107_: u8 = 0;
                            v___x_2106_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3;
                            v___x_2107_ = lean_string_dec_eq(v_str_2098_, v___x_2106_);
                            if v___x_2107_ == 0 {
                                return v___y_2093_;
                            } else {
                                return v_suppressElabErrors_2094_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2108_ = leanh::lean_ctor_get(v_pre_2097_, 0);
                        if leanh::lean_obj_tag(v_pre_2108_) == 0 {
                            let mut v_str_2109_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2110_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2111_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2112_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2113_: u8 = 0;
                            v_str_2109_ = leanh::lean_ctor_get(v_x_2095_, 1);
                            v_str_2110_ = leanh::lean_ctor_get(v_pre_2096_, 1);
                            v_str_2111_ = leanh::lean_ctor_get(v_pre_2097_, 1);
                            v___x_2112_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4;
                            v___x_2113_ = lean_string_dec_eq(v_str_2111_, v___x_2112_);
                            if v___x_2113_ == 0 {
                                return v___y_2093_;
                            } else {
                                let mut v___x_2114_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2115_: u8 = 0;
                                v___x_2114_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5;
                                v___x_2115_ = lean_string_dec_eq(v_str_2110_, v___x_2114_);
                                if v___x_2115_ == 0 {
                                    return v___y_2093_;
                                } else {
                                    let mut v___x_2116_: *mut leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_2117_: u8 = 0;
                                    v___x_2116_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6;
                                    v___x_2117_ = lean_string_dec_eq(v_str_2109_, v___x_2116_);
                                    if v___x_2117_ == 0 {
                                        return v___y_2093_;
                                    } else {
                                        return v_suppressElabErrors_2094_;
                                    }
                                }
                            }
                        } else {
                            return v___y_2093_;
                        }
                    }
                    _ => {
                        return v___y_2093_;
                    }
                }
            }
            0 => {
                let mut v_str_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2120_: u8 = 0;
                v_str_2118_ = leanh::lean_ctor_get(v_x_2095_, 1);
                v___x_2119_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7;
                v___x_2120_ = lean_string_dec_eq(v_str_2118_, v___x_2119_);
                if v___x_2120_ == 0 {
                    return v___y_2093_;
                } else {
                    return v_suppressElabErrors_2094_;
                }
            }
            _ => {
                return v___y_2093_;
            }
        }
    } else {
        return v___y_2093_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___boxed(
    mut v___y_2121_: *mut leanh::LeanObject,
    mut v_suppressElabErrors_2122_: *mut leanh::LeanObject,
    mut v_x_2123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3856__boxed_2124_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2125_: u8 = 0;
    let mut v_res_2126_: u8 = 0;
    let mut v_r_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___y_3856__boxed_2124_ = (leanh::lean_unbox(v___y_2121_) as u8);
    v_suppressElabErrors_boxed_2125_ = (leanh::lean_unbox(v_suppressElabErrors_2122_) as u8);
    v_res_2126_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0(v___y_3856__boxed_2124_, v_suppressElabErrors_boxed_2125_, v_x_2123_);
    leanh::lean_dec(v_x_2123_);
    v_r_2127_ = leanh::lean_box((v_res_2126_) as usize);
    return v_r_2127_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(
    mut v_ref_2129_: *mut leanh::LeanObject,
    mut v_msgData_2130_: *mut leanh::LeanObject,
    mut v_severity_2131_: u8,
    mut v_isSilent_2132_: u8,
    mut v___y_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
    mut v___y_2135_: *mut leanh::LeanObject,
    mut v___y_2136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2139_: u8 = 0;
    let mut v___y_2140_: u8 = 0;
    let mut v___y_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v___y_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: u8 = 0;
    let mut v___y_2177_: u8 = 0;
    let mut v___y_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: u8 = 0;
    let mut v___y_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v___y_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: u8 = 0;
    let mut v___y_2202_: u8 = 0;
    let mut v___y_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: u8 = 0;
    let mut v___y_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2212_: u8 = 0;
    let mut v___y_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2214_: u8 = 0;
    let mut v___y_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2217_: u8 = 0;
    let mut v_ref_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___y_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: u8 = 0;
    let mut v___y_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: u8 = 0;
    let mut v___y_2230_: u8 = 0;
    let mut v___y_2232_: u8 = 0;
    let mut v_fileName_2233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2237_: u8 = 0;
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: u8 = 0;
    let mut v___x_2248_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2222_ = 2;
                v___x_2247_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2131_, v___x_2222_);
                if v___x_2247_ == 0 {
                    v___y_2232_ = v___x_2247_;
                    state = 10;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_msgData_2130_);
                    v___x_2248_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2130_);
                    v___y_2232_ = v___x_2248_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2148_ = lean_st_ref_take(v___y_2147_);
                v_currNamespace_2149_ = leanh::lean_ctor_get(v___y_2146_, 6);
                v_openDecls_2150_ = leanh::lean_ctor_get(v___y_2146_, 7);
                v_env_2151_ = leanh::lean_ctor_get(v___x_2148_, 0);
                v_nextMacroScope_2152_ = leanh::lean_ctor_get(v___x_2148_, 1);
                v_ngen_2153_ = leanh::lean_ctor_get(v___x_2148_, 2);
                v_auxDeclNGen_2154_ = leanh::lean_ctor_get(v___x_2148_, 3);
                v_traceState_2155_ = leanh::lean_ctor_get(v___x_2148_, 4);
                v_cache_2156_ = leanh::lean_ctor_get(v___x_2148_, 5);
                v_messages_2157_ = leanh::lean_ctor_get(v___x_2148_, 6);
                v_infoState_2158_ = leanh::lean_ctor_get(v___x_2148_, 7);
                v_snapshotTasks_2159_ = leanh::lean_ctor_get(v___x_2148_, 8);
                v_isSharedCheck_2173_ = (!leanh::lean_is_exclusive(v___x_2148_)) as u8;
                if v_isSharedCheck_2173_ == 0 {
                    v___x_2161_ = v___x_2148_;
                    v_isShared_2162_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2159_);
                    leanh::lean_inc(v_infoState_2158_);
                    leanh::lean_inc(v_messages_2157_);
                    leanh::lean_inc(v_cache_2156_);
                    leanh::lean_inc(v_traceState_2155_);
                    leanh::lean_inc(v_auxDeclNGen_2154_);
                    leanh::lean_inc(v_ngen_2153_);
                    leanh::lean_inc(v_nextMacroScope_2152_);
                    leanh::lean_inc(v_env_2151_);
                    leanh::lean_dec(v___x_2148_);
                    v___x_2161_ = leanh::lean_box(0);
                    v_isShared_2162_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_openDecls_2150_);
                leanh::lean_inc(v_currNamespace_2149_);
                v___x_2163_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2163_, 0, v_currNamespace_2149_);
                leanh::lean_ctor_set(v___x_2163_, 1, v_openDecls_2150_);
                v___x_2164_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2164_, 0, v___x_2163_);
                leanh::lean_ctor_set(v___x_2164_, 1, v___y_2141_);
                leanh::lean_inc_ref(v___y_2143_);
                leanh::lean_inc_ref(v___y_2145_);
                v___x_2165_ = leanh::lean_alloc_ctor(0, 5, (3) as u32);
                leanh::lean_ctor_set(v___x_2165_, 0, v___y_2145_);
                leanh::lean_ctor_set(v___x_2165_, 1, v___y_2142_);
                leanh::lean_ctor_set(v___x_2165_, 2, v___y_2144_);
                leanh::lean_ctor_set(v___x_2165_, 3, v___y_2143_);
                leanh::lean_ctor_set(v___x_2165_, 4, v___x_2164_);
                leanh::lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5) as u32,
                    v___y_2140_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2139_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2132_,
                );
                v___x_2166_ = l_Lean_MessageLog_add(v___x_2165_, v_messages_2157_);
                if v_isShared_2162_ == 0 {
                    leanh::lean_ctor_set(v___x_2161_, 6, v___x_2166_);
                    v___x_2168_ = v___x_2161_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_env_2151_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_nextMacroScope_2152_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_ngen_2153_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_auxDeclNGen_2154_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_traceState_2155_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_cache_2156_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 6, v___x_2166_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_infoState_2158_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_snapshotTasks_2159_);
                    v___x_2168_ = v_reuseFailAlloc_2172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2169_ = lean_st_ref_set(v___y_2147_, v___x_2168_);
                v___x_2170_ = leanh::lean_box(0);
                v___x_2171_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
                return v___x_2171_;
            }
            4 => {
                v___x_2183_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2130_,
                    );
                v___x_2184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v___x_2183_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
                v_a_2185_ = leanh::lean_ctor_get(v___x_2184_, 0);
                v_isSharedCheck_2198_ = (!leanh::lean_is_exclusive(v___x_2184_)) as u8;
                if v_isSharedCheck_2198_ == 0 {
                    v___x_2187_ = v___x_2184_;
                    v_isShared_2188_ = v_isSharedCheck_2198_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2185_);
                    leanh::lean_dec(v___x_2184_);
                    v___x_2187_ = leanh::lean_box(0);
                    v_isShared_2188_ = v_isSharedCheck_2198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                leanh::lean_inc_ref_n(v___y_2180_, 2);
                v___x_2189_ = l_Lean_FileMap_toPosition(v___y_2180_, v___y_2178_);
                leanh::lean_dec(v___y_2178_);
                v___x_2190_ = l_Lean_FileMap_toPosition(v___y_2180_, v___y_2182_);
                leanh::lean_dec(v___y_2182_);
                v___x_2191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2191_, 0, v___x_2190_);
                v___x_2192_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0;
                if v___y_2179_ == 0 {
                    leanh::lean_del_object(v___x_2187_);
                    leanh::lean_dec_ref(v___y_2175_);
                    v___y_2139_ = v___y_2176_;
                    v___y_2140_ = v___y_2177_;
                    v___y_2141_ = v_a_2185_;
                    v___y_2142_ = v___x_2189_;
                    v___y_2143_ = v___x_2192_;
                    v___y_2144_ = v___x_2191_;
                    v___y_2145_ = v___y_2181_;
                    v___y_2146_ = v___y_2135_;
                    v___y_2147_ = v___y_2136_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2185_);
                    v___x_2193_ = l_Lean_MessageData_hasTag(v___y_2175_, v_a_2185_);
                    if v___x_2193_ == 0 {
                        leanh::lean_dec_ref_known(v___x_2191_, 1);
                        leanh::lean_dec_ref(v___x_2189_);
                        leanh::lean_dec(v_a_2185_);
                        v___x_2194_ = leanh::lean_box(0);
                        if v_isShared_2188_ == 0 {
                            leanh::lean_ctor_set(v___x_2187_, 0, v___x_2194_);
                            v___x_2196_ = v___x_2187_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2197_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
                            v___x_2196_ = v_reuseFailAlloc_2197_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_2187_);
                        v___y_2139_ = v___y_2176_;
                        v___y_2140_ = v___y_2177_;
                        v___y_2141_ = v_a_2185_;
                        v___y_2142_ = v___x_2189_;
                        v___y_2143_ = v___x_2192_;
                        v___y_2144_ = v___x_2191_;
                        v___y_2145_ = v___y_2181_;
                        v___y_2146_ = v___y_2135_;
                        v___y_2147_ = v___y_2136_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_2196_;
            }
            7 => {
                v___x_2208_ = l_Lean_Syntax_getTailPos_x3f(v___y_2203_, v___y_2202_);
                leanh::lean_dec(v___y_2203_);
                if leanh::lean_obj_tag(v___x_2208_) == 0 {
                    leanh::lean_inc(v___y_2207_);
                    v___y_2175_ = v___y_2200_;
                    v___y_2176_ = v___y_2201_;
                    v___y_2177_ = v___y_2202_;
                    v___y_2178_ = v___y_2207_;
                    v___y_2179_ = v___y_2205_;
                    v___y_2180_ = v___y_2204_;
                    v___y_2181_ = v___y_2206_;
                    v___y_2182_ = v___y_2207_;
                    state = 4;
                    continue;
                } else {
                    v_val_2209_ = leanh::lean_ctor_get(v___x_2208_, 0);
                    leanh::lean_inc(v_val_2209_);
                    leanh::lean_dec_ref_known(v___x_2208_, 1);
                    v___y_2175_ = v___y_2200_;
                    v___y_2176_ = v___y_2201_;
                    v___y_2177_ = v___y_2202_;
                    v___y_2178_ = v___y_2207_;
                    v___y_2179_ = v___y_2205_;
                    v___y_2180_ = v___y_2204_;
                    v___y_2181_ = v___y_2206_;
                    v___y_2182_ = v_val_2209_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_2218_ = l_Lean_replaceRef(v_ref_2129_, v___y_2213_);
                v___x_2219_ = l_Lean_Syntax_getPos_x3f(v_ref_2218_, v___y_2212_);
                if leanh::lean_obj_tag(v___x_2219_) == 0 {
                    v___x_2220_ = leanh::lean_unsigned_to_nat(0);
                    v___y_2200_ = v___y_2211_;
                    v___y_2201_ = v___y_2217_;
                    v___y_2202_ = v___y_2212_;
                    v___y_2203_ = v_ref_2218_;
                    v___y_2204_ = v___y_2215_;
                    v___y_2205_ = v___y_2214_;
                    v___y_2206_ = v___y_2216_;
                    v___y_2207_ = v___x_2220_;
                    state = 7;
                    continue;
                } else {
                    v_val_2221_ = leanh::lean_ctor_get(v___x_2219_, 0);
                    leanh::lean_inc(v_val_2221_);
                    leanh::lean_dec_ref_known(v___x_2219_, 1);
                    v___y_2200_ = v___y_2211_;
                    v___y_2201_ = v___y_2217_;
                    v___y_2202_ = v___y_2212_;
                    v___y_2203_ = v_ref_2218_;
                    v___y_2204_ = v___y_2215_;
                    v___y_2205_ = v___y_2214_;
                    v___y_2206_ = v___y_2216_;
                    v___y_2207_ = v_val_2221_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_2230_ == 0 {
                    v___y_2211_ = v___y_2224_;
                    v___y_2212_ = v___y_2229_;
                    v___y_2213_ = v___y_2225_;
                    v___y_2214_ = v___y_2227_;
                    v___y_2215_ = v___y_2226_;
                    v___y_2216_ = v___y_2228_;
                    v___y_2217_ = v_severity_2131_;
                    state = 8;
                    continue;
                } else {
                    v___y_2211_ = v___y_2224_;
                    v___y_2212_ = v___y_2229_;
                    v___y_2213_ = v___y_2225_;
                    v___y_2214_ = v___y_2227_;
                    v___y_2215_ = v___y_2226_;
                    v___y_2216_ = v___y_2228_;
                    v___y_2217_ = v___x_2222_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_2232_ == 0 {
                    v_fileName_2233_ = leanh::lean_ctor_get(v___y_2135_, 0);
                    v_fileMap_2234_ = leanh::lean_ctor_get(v___y_2135_, 1);
                    v_options_2235_ = leanh::lean_ctor_get(v___y_2135_, 2);
                    v_ref_2236_ = leanh::lean_ctor_get(v___y_2135_, 5);
                    v_suppressElabErrors_2237_ = leanh::lean_ctor_get_uint8(
                        v___y_2135_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2238_ = leanh::lean_box((v___y_2232_) as usize);
                    v___x_2239_ = leanh::lean_box((v_suppressElabErrors_2237_) as usize);
                    v___f_2240_ = leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2240_, 0, v___x_2238_);
                    leanh::lean_closure_set(v___f_2240_, 1, v___x_2239_);
                    v___x_2241_ = 1;
                    v___x_2242_ = l_Lean_instBEqMessageSeverity_beq(v_severity_2131_, v___x_2241_);
                    if v___x_2242_ == 0 {
                        v___y_2224_ = v___f_2240_;
                        v___y_2225_ = v_ref_2236_;
                        v___y_2226_ = v_fileMap_2234_;
                        v___y_2227_ = v_suppressElabErrors_2237_;
                        v___y_2228_ = v_fileName_2233_;
                        v___y_2229_ = v___y_2232_;
                        v___y_2230_ = v___x_2242_;
                        state = 9;
                        continue;
                    } else {
                        v___x_2243_ = l_Lean_warningAsError;
                        v___x_2244_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_options_2235_, v___x_2243_);
                        v___y_2224_ = v___f_2240_;
                        v___y_2225_ = v_ref_2236_;
                        v___y_2226_ = v_fileMap_2234_;
                        v___y_2227_ = v_suppressElabErrors_2237_;
                        v___y_2228_ = v_fileName_2233_;
                        v___y_2229_ = v___y_2232_;
                        v___y_2230_ = v___x_2244_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msgData_2130_);
                    v___x_2245_ = leanh::lean_box(0);
                    v___x_2246_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
                    return v___x_2246_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_ref_2249_: *mut leanh::LeanObject,
    mut v_msgData_2250_: *mut leanh::LeanObject,
    mut v_severity_2251_: *mut leanh::LeanObject,
    mut v_isSilent_2252_: *mut leanh::LeanObject,
    mut v___y_2253_: *mut leanh::LeanObject,
    mut v___y_2254_: *mut leanh::LeanObject,
    mut v___y_2255_: *mut leanh::LeanObject,
    mut v___y_2256_: *mut leanh::LeanObject,
    mut v___y_2257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2258_: u8 = 0;
    let mut v_isSilent_boxed_2259_: u8 = 0;
    let mut v_res_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2258_ = (leanh::lean_unbox(v_severity_2251_) as u8);
    v_isSilent_boxed_2259_ = (leanh::lean_unbox(v_isSilent_2252_) as u8);
    v_res_2260_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(v_ref_2249_, v_msgData_2250_, v_severity_boxed_2258_, v_isSilent_boxed_2259_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
    leanh::lean_dec(v___y_2256_);
    leanh::lean_dec_ref(v___y_2255_);
    leanh::lean_dec(v___y_2254_);
    leanh::lean_dec_ref(v___y_2253_);
    leanh::lean_dec(v_ref_2249_);
    return v_res_2260_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1(
    mut v_msgData_2261_: *mut leanh::LeanObject,
    mut v_severity_2262_: u8,
    mut v_isSilent_2263_: u8,
    mut v___y_2264_: *mut leanh::LeanObject,
    mut v___y_2265_: *mut leanh::LeanObject,
    mut v___y_2266_: *mut leanh::LeanObject,
    mut v___y_2267_: *mut leanh::LeanObject,
    mut v___y_2268_: *mut leanh::LeanObject,
    mut v___y_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2271_ = leanh::lean_ctor_get(v___y_2268_, 5);
    v___x_2272_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(v_ref_2271_, v_msgData_2261_, v_severity_2262_, v_isSilent_2263_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
    return v___x_2272_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1___boxed(
    mut v_msgData_2273_: *mut leanh::LeanObject,
    mut v_severity_2274_: *mut leanh::LeanObject,
    mut v_isSilent_2275_: *mut leanh::LeanObject,
    mut v___y_2276_: *mut leanh::LeanObject,
    mut v___y_2277_: *mut leanh::LeanObject,
    mut v___y_2278_: *mut leanh::LeanObject,
    mut v___y_2279_: *mut leanh::LeanObject,
    mut v___y_2280_: *mut leanh::LeanObject,
    mut v___y_2281_: *mut leanh::LeanObject,
    mut v___y_2282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2283_: u8 = 0;
    let mut v_isSilent_boxed_2284_: u8 = 0;
    let mut v_res_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2283_ = (leanh::lean_unbox(v_severity_2274_) as u8);
    v_isSilent_boxed_2284_ = (leanh::lean_unbox(v_isSilent_2275_) as u8);
    v_res_2285_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1(v_msgData_2273_, v_severity_boxed_2283_, v_isSilent_boxed_2284_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
    leanh::lean_dec(v___y_2281_);
    leanh::lean_dec_ref(v___y_2280_);
    leanh::lean_dec(v___y_2279_);
    leanh::lean_dec_ref(v___y_2278_);
    leanh::lean_dec(v___y_2277_);
    leanh::lean_dec_ref(v___y_2276_);
    return v_res_2285_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(
    mut v_msgData_2286_: *mut leanh::LeanObject,
    mut v___y_2287_: *mut leanh::LeanObject,
    mut v___y_2288_: *mut leanh::LeanObject,
    mut v___y_2289_: *mut leanh::LeanObject,
    mut v___y_2290_: *mut leanh::LeanObject,
    mut v___y_2291_: *mut leanh::LeanObject,
    mut v___y_2292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2294_: u8 = 0;
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = 0;
    v___x_2295_ = 0;
    v___x_2296_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1(v_msgData_2286_, v___x_2294_, v___x_2295_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
    return v___x_2296_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1___boxed(
    mut v_msgData_2297_: *mut leanh::LeanObject,
    mut v___y_2298_: *mut leanh::LeanObject,
    mut v___y_2299_: *mut leanh::LeanObject,
    mut v___y_2300_: *mut leanh::LeanObject,
    mut v___y_2301_: *mut leanh::LeanObject,
    mut v___y_2302_: *mut leanh::LeanObject,
    mut v___y_2303_: *mut leanh::LeanObject,
    mut v___y_2304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(
        v_msgData_2297_,
        v___y_2298_,
        v___y_2299_,
        v___y_2300_,
        v___y_2301_,
        v___y_2302_,
        v___y_2303_,
    );
    leanh::lean_dec(v___y_2303_);
    leanh::lean_dec_ref(v___y_2302_);
    leanh::lean_dec(v___y_2301_);
    leanh::lean_dec_ref(v___y_2300_);
    leanh::lean_dec(v___y_2299_);
    leanh::lean_dec_ref(v___y_2298_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0(
    mut v___x_2306_: u8,
    mut v_stx_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
    mut v___y_2309_: *mut leanh::LeanObject,
    mut v___y_2310_: *mut leanh::LeanObject,
    mut v___y_2311_: *mut leanh::LeanObject,
    mut v___y_2312_: *mut leanh::LeanObject,
    mut v___y_2313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_a_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_a_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2306_ == 0 {
                    v___x_2315_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
                    return v___x_2315_;
                } else {
                    v___x_2316_ = leanh::lean_unsigned_to_nat(1);
                    v_t_2317_ = l_Lean_Syntax_getArg(v_stx_2307_, v___x_2316_);
                    v___x_2318_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(v_t_2317_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                    if leanh::lean_obj_tag(v___x_2318_) == 0 {
                        v_a_2319_ = leanh::lean_ctor_get(v___x_2318_, 0);
                        leanh::lean_inc(v_a_2319_);
                        leanh::lean_dec_ref_known(v___x_2318_, 1);
                        v___x_2320_ = 0;
                        v___x_2321_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(v_a_2319_, v___x_2320_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                        if leanh::lean_obj_tag(v___x_2321_) == 0 {
                            v_a_2322_ = leanh::lean_ctor_get(v___x_2321_, 0);
                            leanh::lean_inc(v_a_2322_);
                            leanh::lean_dec_ref_known(v___x_2321_, 1);
                            v___x_2323_ = l_Lean_Meta_DiscrTree_keysAsPattern(
                                v_a_2322_,
                                v___y_2312_,
                                v___y_2313_,
                            );
                            if leanh::lean_obj_tag(v___x_2323_) == 0 {
                                v_a_2324_ = leanh::lean_ctor_get(v___x_2323_, 0);
                                leanh::lean_inc(v_a_2324_);
                                leanh::lean_dec_ref_known(v___x_2323_, 1);
                                v___x_2325_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(v_a_2324_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                                return v___x_2325_;
                            } else {
                                v_a_2326_ = leanh::lean_ctor_get(v___x_2323_, 0);
                                v_isSharedCheck_2333_ =
                                    (!leanh::lean_is_exclusive(v___x_2323_)) as u8;
                                if v_isSharedCheck_2333_ == 0 {
                                    v___x_2328_ = v___x_2323_;
                                    v_isShared_2329_ = v_isSharedCheck_2333_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2326_);
                                    leanh::lean_dec(v___x_2323_);
                                    v___x_2328_ = leanh::lean_box(0);
                                    v_isShared_2329_ = v_isSharedCheck_2333_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_2334_ = leanh::lean_ctor_get(v___x_2321_, 0);
                            v_isSharedCheck_2341_ =
                                (!leanh::lean_is_exclusive(v___x_2321_)) as u8;
                            if v_isSharedCheck_2341_ == 0 {
                                v___x_2336_ = v___x_2321_;
                                v_isShared_2337_ = v_isSharedCheck_2341_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2334_);
                                leanh::lean_dec(v___x_2321_);
                                v___x_2336_ = leanh::lean_box(0);
                                v_isShared_2337_ = v_isSharedCheck_2341_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_2342_ = leanh::lean_ctor_get(v___x_2318_, 0);
                        v_isSharedCheck_2349_ =
                            (!leanh::lean_is_exclusive(v___x_2318_)) as u8;
                        if v_isSharedCheck_2349_ == 0 {
                            v___x_2344_ = v___x_2318_;
                            v_isShared_2345_ = v_isSharedCheck_2349_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2342_);
                            leanh::lean_dec(v___x_2318_);
                            v___x_2344_ = leanh::lean_box(0);
                            v_isShared_2345_ = v_isSharedCheck_2349_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2329_ == 0 {
                    v___x_2331_ = v___x_2328_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2332_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
                    v___x_2331_ = v_reuseFailAlloc_2332_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2331_;
            }
            3 => {
                if v_isShared_2337_ == 0 {
                    v___x_2339_ = v___x_2336_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2339_;
            }
            5 => {
                if v_isShared_2345_ == 0 {
                    v___x_2347_ = v___x_2344_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2348_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
                    v___x_2347_ = v_reuseFailAlloc_2348_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2347_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0___boxed(
    mut v___x_2350_: *mut leanh::LeanObject,
    mut v_stx_2351_: *mut leanh::LeanObject,
    mut v___y_2352_: *mut leanh::LeanObject,
    mut v___y_2353_: *mut leanh::LeanObject,
    mut v___y_2354_: *mut leanh::LeanObject,
    mut v___y_2355_: *mut leanh::LeanObject,
    mut v___y_2356_: *mut leanh::LeanObject,
    mut v___y_2357_: *mut leanh::LeanObject,
    mut v___y_2358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4185__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4185__boxed_2359_ = (leanh::lean_unbox(v___x_2350_) as u8);
    v_res_2360_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0(
        v___x_4185__boxed_2359_,
        v_stx_2351_,
        v___y_2352_,
        v___y_2353_,
        v___y_2354_,
        v___y_2355_,
        v___y_2356_,
        v___y_2357_,
    );
    leanh::lean_dec(v___y_2357_);
    leanh::lean_dec_ref(v___y_2356_);
    leanh::lean_dec(v___y_2355_);
    leanh::lean_dec_ref(v___y_2354_);
    leanh::lean_dec(v___y_2353_);
    leanh::lean_dec_ref(v___y_2352_);
    leanh::lean_dec(v_stx_2351_);
    return v_res_2360_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(
    mut v_stx_2368_: *mut leanh::LeanObject,
    mut v_a_2369_: *mut leanh::LeanObject,
    mut v_a_2370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3;
    leanh::lean_inc(v_stx_2368_);
    v___x_2373_ = l_Lean_Syntax_isOfKind(v_stx_2368_, v___x_2372_);
    v___x_2374_ = leanh::lean_box((v___x_2373_) as usize);
    v___y_2375_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___y_2375_, 0, v___x_2374_);
    leanh::lean_closure_set(v___y_2375_, 1, v_stx_2368_);
    v___x_2376_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_2375_, v_a_2369_, v_a_2370_);
    return v___x_2376_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed(
    mut v_stx_2377_: *mut leanh::LeanObject,
    mut v_a_2378_: *mut leanh::LeanObject,
    mut v_a_2379_: *mut leanh::LeanObject,
    mut v_a_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ =
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(v_stx_2377_, v_a_2378_, v_a_2379_);
    leanh::lean_dec(v_a_2379_);
    leanh::lean_dec_ref(v_a_2378_);
    return v_res_2381_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2(
    mut v_ref_2382_: *mut leanh::LeanObject,
    mut v_msgData_2383_: *mut leanh::LeanObject,
    mut v_severity_2384_: u8,
    mut v_isSilent_2385_: u8,
    mut v___y_2386_: *mut leanh::LeanObject,
    mut v___y_2387_: *mut leanh::LeanObject,
    mut v___y_2388_: *mut leanh::LeanObject,
    mut v___y_2389_: *mut leanh::LeanObject,
    mut v___y_2390_: *mut leanh::LeanObject,
    mut v___y_2391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(v_ref_2382_, v_msgData_2383_, v_severity_2384_, v_isSilent_2385_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
    return v___x_2393_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___boxed(
    mut v_ref_2394_: *mut leanh::LeanObject,
    mut v_msgData_2395_: *mut leanh::LeanObject,
    mut v_severity_2396_: *mut leanh::LeanObject,
    mut v_isSilent_2397_: *mut leanh::LeanObject,
    mut v___y_2398_: *mut leanh::LeanObject,
    mut v___y_2399_: *mut leanh::LeanObject,
    mut v___y_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
    mut v___y_2402_: *mut leanh::LeanObject,
    mut v___y_2403_: *mut leanh::LeanObject,
    mut v___y_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_severity_boxed_2405_: u8 = 0;
    let mut v_isSilent_boxed_2406_: u8 = 0;
    let mut v_res_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2405_ = (leanh::lean_unbox(v_severity_2396_) as u8);
    v_isSilent_boxed_2406_ = (leanh::lean_unbox(v_isSilent_2397_) as u8);
    v_res_2407_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2(v_ref_2394_, v_msgData_2395_, v_severity_boxed_2405_, v_isSilent_boxed_2406_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
    leanh::lean_dec(v___y_2403_);
    leanh::lean_dec_ref(v___y_2402_);
    leanh::lean_dec(v___y_2401_);
    leanh::lean_dec_ref(v___y_2400_);
    leanh::lean_dec(v___y_2399_);
    leanh::lean_dec_ref(v___y_2398_);
    leanh::lean_dec(v_ref_2394_);
    return v_res_2407_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1()
-> *mut leanh::LeanObject {
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2417_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2418_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3;
    v___x_2419_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2;
    v___x_2420_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2421_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2417_,
        v___x_2418_,
        v___x_2419_,
        v___x_2420_,
    );
    return v___x_2421_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___boxed(
    mut v_a_2422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1();
    return v_res_2423_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0(
    mut v___x_2424_: u8,
    mut v_stx_2425_: *mut leanh::LeanObject,
    mut v___x_2426_: u8,
    mut v___y_2427_: *mut leanh::LeanObject,
    mut v___y_2428_: *mut leanh::LeanObject,
    mut v___y_2429_: *mut leanh::LeanObject,
    mut v___y_2430_: *mut leanh::LeanObject,
    mut v___y_2431_: *mut leanh::LeanObject,
    mut v___y_2432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut v_a_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_a_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2424_ == 0 {
                    v___x_2434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
                    return v___x_2434_;
                } else {
                    v___x_2435_ = leanh::lean_unsigned_to_nat(1);
                    v_t_2436_ = l_Lean_Syntax_getArg(v_stx_2425_, v___x_2435_);
                    v___x_2437_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(v_t_2436_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
                    if leanh::lean_obj_tag(v___x_2437_) == 0 {
                        v_a_2438_ = leanh::lean_ctor_get(v___x_2437_, 0);
                        leanh::lean_inc(v_a_2438_);
                        leanh::lean_dec_ref_known(v___x_2437_, 1);
                        v___x_2439_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(v_a_2438_, v___x_2426_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
                        if leanh::lean_obj_tag(v___x_2439_) == 0 {
                            v_a_2440_ = leanh::lean_ctor_get(v___x_2439_, 0);
                            leanh::lean_inc(v_a_2440_);
                            leanh::lean_dec_ref_known(v___x_2439_, 1);
                            v___x_2441_ = l_Lean_Meta_DiscrTree_keysAsPattern(
                                v_a_2440_,
                                v___y_2431_,
                                v___y_2432_,
                            );
                            if leanh::lean_obj_tag(v___x_2441_) == 0 {
                                v_a_2442_ = leanh::lean_ctor_get(v___x_2441_, 0);
                                leanh::lean_inc(v_a_2442_);
                                leanh::lean_dec_ref_known(v___x_2441_, 1);
                                v___x_2443_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(v_a_2442_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
                                return v___x_2443_;
                            } else {
                                v_a_2444_ = leanh::lean_ctor_get(v___x_2441_, 0);
                                v_isSharedCheck_2451_ =
                                    (!leanh::lean_is_exclusive(v___x_2441_)) as u8;
                                if v_isSharedCheck_2451_ == 0 {
                                    v___x_2446_ = v___x_2441_;
                                    v_isShared_2447_ = v_isSharedCheck_2451_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2444_);
                                    leanh::lean_dec(v___x_2441_);
                                    v___x_2446_ = leanh::lean_box(0);
                                    v_isShared_2447_ = v_isSharedCheck_2451_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_2452_ = leanh::lean_ctor_get(v___x_2439_, 0);
                            v_isSharedCheck_2459_ =
                                (!leanh::lean_is_exclusive(v___x_2439_)) as u8;
                            if v_isSharedCheck_2459_ == 0 {
                                v___x_2454_ = v___x_2439_;
                                v_isShared_2455_ = v_isSharedCheck_2459_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2452_);
                                leanh::lean_dec(v___x_2439_);
                                v___x_2454_ = leanh::lean_box(0);
                                v_isShared_2455_ = v_isSharedCheck_2459_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_2460_ = leanh::lean_ctor_get(v___x_2437_, 0);
                        v_isSharedCheck_2467_ =
                            (!leanh::lean_is_exclusive(v___x_2437_)) as u8;
                        if v_isSharedCheck_2467_ == 0 {
                            v___x_2462_ = v___x_2437_;
                            v_isShared_2463_ = v_isSharedCheck_2467_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2460_);
                            leanh::lean_dec(v___x_2437_);
                            v___x_2462_ = leanh::lean_box(0);
                            v_isShared_2463_ = v_isSharedCheck_2467_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2447_ == 0 {
                    v___x_2449_ = v___x_2446_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
                    v___x_2449_ = v_reuseFailAlloc_2450_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2449_;
            }
            3 => {
                if v_isShared_2455_ == 0 {
                    v___x_2457_ = v___x_2454_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
                    v___x_2457_ = v_reuseFailAlloc_2458_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2457_;
            }
            5 => {
                if v_isShared_2463_ == 0 {
                    v___x_2465_ = v___x_2462_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0___boxed(
    mut v___x_2468_: *mut leanh::LeanObject,
    mut v_stx_2469_: *mut leanh::LeanObject,
    mut v___x_2470_: *mut leanh::LeanObject,
    mut v___y_2471_: *mut leanh::LeanObject,
    mut v___y_2472_: *mut leanh::LeanObject,
    mut v___y_2473_: *mut leanh::LeanObject,
    mut v___y_2474_: *mut leanh::LeanObject,
    mut v___y_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
    mut v___y_2477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_589__boxed_2478_: u8 = 0;
    let mut v___x_590__boxed_2479_: u8 = 0;
    let mut v_res_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_589__boxed_2478_ = (leanh::lean_unbox(v___x_2468_) as u8);
    v___x_590__boxed_2479_ = (leanh::lean_unbox(v___x_2470_) as u8);
    v_res_2480_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0(
        v___x_589__boxed_2478_,
        v_stx_2469_,
        v___x_590__boxed_2479_,
        v___y_2471_,
        v___y_2472_,
        v___y_2473_,
        v___y_2474_,
        v___y_2475_,
        v___y_2476_,
    );
    leanh::lean_dec(v___y_2476_);
    leanh::lean_dec_ref(v___y_2475_);
    leanh::lean_dec(v___y_2474_);
    leanh::lean_dec_ref(v___y_2473_);
    leanh::lean_dec(v___y_2472_);
    leanh::lean_dec_ref(v___y_2471_);
    leanh::lean_dec(v_stx_2469_);
    return v_res_2480_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(
    mut v_stx_2486_: *mut leanh::LeanObject,
    mut v_a_2487_: *mut leanh::LeanObject,
    mut v_a_2488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1;
    leanh::lean_inc(v_stx_2486_);
    v___x_2491_ = l_Lean_Syntax_isOfKind(v_stx_2486_, v___x_2490_);
    v___x_2492_ = 1;
    v___x_2493_ = leanh::lean_box((v___x_2491_) as usize);
    v___x_2494_ = leanh::lean_box((v___x_2492_) as usize);
    v___y_2495_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        3,
    );
    leanh::lean_closure_set(v___y_2495_, 0, v___x_2493_);
    leanh::lean_closure_set(v___y_2495_, 1, v_stx_2486_);
    leanh::lean_closure_set(v___y_2495_, 2, v___x_2494_);
    v___x_2496_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_2495_, v_a_2487_, v_a_2488_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed(
    mut v_stx_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
    mut v_a_2499_: *mut leanh::LeanObject,
    mut v_a_2500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ =
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(v_stx_2497_, v_a_2498_, v_a_2499_);
    leanh::lean_dec(v_a_2499_);
    leanh::lean_dec_ref(v_a_2498_);
    return v_res_2501_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1()
-> *mut leanh::LeanObject {
    let mut v___x_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2511_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1;
    v___x_2512_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1;
    v___x_2513_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2514_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2510_,
        v___x_2511_,
        v___x_2512_,
        v___x_2513_,
    );
    return v___x_2514_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___boxed(
    mut v_a_2515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2516_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1();
    return v_res_2516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_DiscrTreeKey(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_DiscrTreeKey(
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
pub unsafe fn initialize_Lean_Elab_Tactic_DiscrTreeKey(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
}