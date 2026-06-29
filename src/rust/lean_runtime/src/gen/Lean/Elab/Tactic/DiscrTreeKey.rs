// Lean compiler output
// Module: Lean.Elab.Tactic.DiscrTreeKey
// Imports: Lean.Elab.Command Lean.Meta.Tactic.Simp.SimpTheorems
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
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_mk_empty_array_with_capacity, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0: u64 = 0;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 102, 102, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__1_value) as *mut crate::leanh::LeanObject,9917798623386220051 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [78, 101, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__3_value) as *mut crate::leanh::LeanObject,6695605208187598753 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 111, 116, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__5_value) as *mut crate::leanh::LeanObject,16612019923665488825 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__7_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value:
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
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__2_value)
            as *mut crate::leanh::LeanObject,
        56916842056113140 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 75, 101, 121, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [101, 118, 97, 108, 68, 105, 115, 99, 114, 84, 114, 101, 101, 75, 101, 121, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,15507137722572484428 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__1_value) as *mut crate::leanh::LeanObject,17543557265682499791 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        15128410572378117509 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [101, 118, 97, 108, 68, 105, 115, 99, 114, 84, 114, 101, 101, 83, 105, 109, 112, 75, 101, 121, 67, 109, 100, 0]};
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,15507137722572484428 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__0_value) as *mut crate::leanh::LeanObject,16162822488894939254 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0()
-> u64 {
    let mut v___x_1259_: u8 = 0;
    let mut v___x_1260_: u64 = 0;
    v___x_1259_ = 2;
    v___x_1260_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1259_);
    return v___x_1260_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(
    mut v_e_1273_: *mut crate::leanh::LeanObject,
    mut v_simp_1274_: u8,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: *mut crate::leanh::LeanObject,
    mut v_a_1277_: *mut crate::leanh::LeanObject,
    mut v_a_1278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v_trackZetaDelta_1302_: u8 = 0;
    let mut v_zetaDeltaSet_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1309_: u8 = 0;
    let mut v_inTypeClassResolution_1310_: u8 = 0;
    let mut v_cacheInferType_1311_: u8 = 0;
    let mut v___x_1312_: u8 = 0;
    let mut v_config_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: u64 = 0;
    let mut v___x_1316_: u64 = 0;
    let mut v___x_1317_: u64 = 0;
    let mut v___x_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: u64 = 0;
    let mut v___x_1321_: u64 = 0;
    let mut v_key_1322_: u64 = 0;
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v_snd_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1334_: u8 = 0;
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u64 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: u8 = 0;
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1370_: u8 = 0;
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1374_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: u8 = 0;
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: u8 = 0;
    let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1398_: u8 = 0;
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1402_: u8 = 0;
    let mut v_isSharedCheck_1403_: u8 = 0;
    let mut v_unused_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1405_: u8 = 0;
    let mut v_unused_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_reuseFailAlloc_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1280_ = l_Lean_Meta_Context_config(v_a_1275_);
                v_foApprox_1281_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 0 as u32);
                v_ctxApprox_1282_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 1 as u32);
                v_quasiPatternApprox_1283_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1280_, 2 as u32);
                v_constApprox_1284_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 3 as u32);
                v_isDefEqStuckEx_1285_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 4 as u32);
                v_unificationHints_1286_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 5 as u32);
                v_proofIrrelevance_1287_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 6 as u32);
                v_assignSyntheticOpaque_1288_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1280_, 7 as u32);
                v_offsetCnstrs_1289_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 8 as u32);
                v_etaStruct_1290_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 10 as u32);
                v_univApprox_1291_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 11 as u32);
                v_iota_1292_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 12 as u32);
                v_beta_1293_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 13 as u32);
                v_proj_1294_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 14 as u32);
                v_zeta_1295_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 15 as u32);
                v_zetaDelta_1296_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 16 as u32);
                v_zetaUnused_1297_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 17 as u32);
                v_zetaHave_1298_ = crate::leanh::lean_ctor_get_uint8(v___x_1280_, 18 as u32);
                v_isSharedCheck_1416_ = (!crate::leanh::lean_is_exclusive(v___x_1280_)) as u8;
                if v_isSharedCheck_1416_ == 0 {
                    v___x_1300_ = v___x_1280_;
                    v_isShared_1301_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1280_);
                    v___x_1300_ = crate::leanh::lean_box(0);
                    v_isShared_1301_ = v_isSharedCheck_1416_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_1302_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1303_ = crate::leanh::lean_ctor_get(v_a_1275_, 1);
                v_lctx_1304_ = crate::leanh::lean_ctor_get(v_a_1275_, 2);
                v_localInstances_1305_ = crate::leanh::lean_ctor_get(v_a_1275_, 3);
                v_defEqCtx_x3f_1306_ = crate::leanh::lean_ctor_get(v_a_1275_, 4);
                v_synthPendingDepth_1307_ = crate::leanh::lean_ctor_get(v_a_1275_, 5);
                v_canUnfold_x3f_1308_ = crate::leanh::lean_ctor_get(v_a_1275_, 6);
                v_univApprox_1309_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1310_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1311_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1275_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1312_ = 2;
                if v_isShared_1301_ == 0 {
                    v_config_1314_ = v___x_1300_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1415_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        0 as u32,
                        v_foApprox_1281_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        1 as u32,
                        v_ctxApprox_1282_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        2 as u32,
                        v_quasiPatternApprox_1283_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        3 as u32,
                        v_constApprox_1284_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        4 as u32,
                        v_isDefEqStuckEx_1285_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        5 as u32,
                        v_unificationHints_1286_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        6 as u32,
                        v_proofIrrelevance_1287_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        7 as u32,
                        v_assignSyntheticOpaque_1288_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        8 as u32,
                        v_offsetCnstrs_1289_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        10 as u32,
                        v_etaStruct_1290_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        11 as u32,
                        v_univApprox_1291_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        12 as u32,
                        v_iota_1292_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        13 as u32,
                        v_beta_1293_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        14 as u32,
                        v_proj_1294_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        15 as u32,
                        v_zeta_1295_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        16 as u32,
                        v_zetaDelta_1296_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1415_,
                        17 as u32,
                        v_zetaUnused_1297_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
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
                crate::leanh::lean_ctor_set_uint8(v_config_1314_, 9 as u32, v___x_1312_);
                v___x_1315_ = l_Lean_Meta_Context_configKey(v_a_1275_);
                v___x_1316_ = 3u64;
                v___x_1317_ = lean_uint64_shift_right(v___x_1315_, v___x_1316_);
                v___x_1318_ = crate::leanh::lean_box(0);
                v___x_1319_ = 0;
                v___x_1320_ = lean_uint64_shift_left(v___x_1317_, v___x_1316_);
                v___x_1321_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0_once), _init_l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__0);
                v_key_1322_ = lean_uint64_lor(v___x_1320_, v___x_1321_);
                v___x_1323_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1323_, 0, v_config_1314_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1323_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_1322_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1308_);
                crate::leanh::lean_inc(v_synthPendingDepth_1307_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1306_);
                crate::leanh::lean_inc_ref(v_localInstances_1305_);
                crate::leanh::lean_inc_ref(v_lctx_1304_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1303_);
                v___x_1324_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                crate::leanh::lean_ctor_set(v___x_1324_, 1, v_zetaDeltaSet_1303_);
                crate::leanh::lean_ctor_set(v___x_1324_, 2, v_lctx_1304_);
                crate::leanh::lean_ctor_set(v___x_1324_, 3, v_localInstances_1305_);
                crate::leanh::lean_ctor_set(v___x_1324_, 4, v_defEqCtx_x3f_1306_);
                crate::leanh::lean_ctor_set(v___x_1324_, 5, v_synthPendingDepth_1307_);
                crate::leanh::lean_ctor_set(v___x_1324_, 6, v_canUnfold_x3f_1308_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1302_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1309_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1310_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1324_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
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
                crate::leanh::lean_dec_ref_known(v___x_1324_, 7);
                if crate::leanh::lean_obj_tag(v___x_1325_) == 0 {
                    v_a_1326_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                    crate::leanh::lean_inc(v_a_1326_);
                    crate::leanh::lean_dec_ref_known(v___x_1325_, 1);
                    v_snd_1327_ = crate::leanh::lean_ctor_get(v_a_1326_, 1);
                    v_isSharedCheck_1405_ = (!crate::leanh::lean_is_exclusive(v_a_1326_)) as u8;
                    if v_isSharedCheck_1405_ == 0 {
                        v_unused_1406_ = crate::leanh::lean_ctor_get(v_a_1326_, 0);
                        crate::leanh::lean_dec(v_unused_1406_);
                        v___x_1329_ = v_a_1326_;
                        v_isShared_1330_ = v_isSharedCheck_1405_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1327_);
                        crate::leanh::lean_dec(v_a_1326_);
                        v___x_1329_ = crate::leanh::lean_box(0);
                        v_isShared_1330_ = v_isSharedCheck_1405_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_1407_ = crate::leanh::lean_ctor_get(v___x_1325_, 0);
                    v_isSharedCheck_1414_ = (!crate::leanh::lean_is_exclusive(v___x_1325_)) as u8;
                    if v_isSharedCheck_1414_ == 0 {
                        v___x_1409_ = v___x_1325_;
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1407_);
                        crate::leanh::lean_dec(v___x_1325_);
                        v___x_1409_ = crate::leanh::lean_box(0);
                        v_isShared_1410_ = v_isSharedCheck_1414_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v_snd_1331_ = crate::leanh::lean_ctor_get(v_snd_1327_, 1);
                v_isSharedCheck_1403_ = (!crate::leanh::lean_is_exclusive(v_snd_1327_)) as u8;
                if v_isSharedCheck_1403_ == 0 {
                    v_unused_1404_ = crate::leanh::lean_ctor_get(v_snd_1327_, 0);
                    crate::leanh::lean_dec(v_unused_1404_);
                    v___x_1333_ = v_snd_1327_;
                    v_isShared_1334_ = v_isSharedCheck_1403_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1331_);
                    crate::leanh::lean_dec(v_snd_1327_);
                    v___x_1333_ = crate::leanh::lean_box(0);
                    v_isShared_1334_ = v_isSharedCheck_1403_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1335_ =
                    l_Lean_Meta_whnfR(v_snd_1331_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
                if crate::leanh::lean_obj_tag(v___x_1335_) == 0 {
                    v_a_1336_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                    crate::leanh::lean_inc(v_a_1336_);
                    crate::leanh::lean_dec_ref_known(v___x_1335_, 1);
                    if v_simp_1274_ == 0 {
                        crate::leanh::lean_del_object(v___x_1333_);
                        crate::leanh::lean_del_object(v___x_1329_);
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
                        v___x_1381_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1382_ = l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1380_, v___x_1381_);
                        if v___x_1382_ == 0 {
                            crate::leanh::lean_del_object(v___x_1333_);
                            crate::leanh::lean_del_object(v___x_1329_);
                            v___y_1338_ = v___x_1318_;
                            state = 5;
                            continue;
                        } else {
                            v___x_1383_ = l_Lean_Expr_appFn_x21(v_a_1336_);
                            v___x_1384_ = l_Lean_Expr_appFn_x21(v___x_1383_);
                            v___x_1385_ = l_Lean_Expr_appArg_x21(v___x_1384_);
                            crate::leanh::lean_dec_ref(v___x_1384_);
                            v___x_1386_ = l_Lean_Expr_appArg_x21(v___x_1383_);
                            crate::leanh::lean_dec_ref(v___x_1383_);
                            v___x_1387_ = l_Lean_Expr_appArg_x21(v_a_1336_);
                            if v_isShared_1334_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1333_, 1, v___x_1387_);
                                crate::leanh::lean_ctor_set(v___x_1333_, 0, v___x_1386_);
                                v___x_1389_ = v___x_1333_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1394_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 0, v___x_1386_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1394_, 1, v___x_1387_);
                                v___x_1389_ = v_reuseFailAlloc_1394_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1333_);
                    crate::leanh::lean_del_object(v___x_1329_);
                    v_a_1395_ = crate::leanh::lean_ctor_get(v___x_1335_, 0);
                    v_isSharedCheck_1402_ = (!crate::leanh::lean_is_exclusive(v___x_1335_)) as u8;
                    if v_isSharedCheck_1402_ == 0 {
                        v___x_1397_ = v___x_1335_;
                        v_isShared_1398_ = v_isSharedCheck_1402_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1395_);
                        crate::leanh::lean_dec(v___x_1335_);
                        v___x_1397_ = crate::leanh::lean_box(0);
                        v_isShared_1398_ = v_isSharedCheck_1402_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1339_ = l_Lean_Meta_simpGlobalConfig;
                v_config_1340_ = crate::leanh::lean_ctor_get(v___x_1339_, 0);
                v___x_1341_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1340_);
                crate::leanh::lean_inc_ref(v_config_1340_);
                v___x_1342_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1342_, 0, v_config_1340_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1342_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1341_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1308_);
                crate::leanh::lean_inc(v_synthPendingDepth_1307_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1306_);
                crate::leanh::lean_inc_ref(v_localInstances_1305_);
                crate::leanh::lean_inc_ref(v_lctx_1304_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1303_);
                v___x_1343_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1343_, 0, v___x_1342_);
                crate::leanh::lean_ctor_set(v___x_1343_, 1, v_zetaDeltaSet_1303_);
                crate::leanh::lean_ctor_set(v___x_1343_, 2, v_lctx_1304_);
                crate::leanh::lean_ctor_set(v___x_1343_, 3, v_localInstances_1305_);
                crate::leanh::lean_ctor_set(v___x_1343_, 4, v_defEqCtx_x3f_1306_);
                crate::leanh::lean_ctor_set(v___x_1343_, 5, v_synthPendingDepth_1307_);
                crate::leanh::lean_ctor_set(v___x_1343_, 6, v_canUnfold_x3f_1308_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1302_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1309_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1310_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1343_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1311_,
                );
                if crate::leanh::lean_obj_tag(v___y_1338_) == 1 {
                    crate::leanh::lean_dec(v_a_1336_);
                    v_val_1344_ = crate::leanh::lean_ctor_get(v___y_1338_, 0);
                    crate::leanh::lean_inc(v_val_1344_);
                    crate::leanh::lean_dec_ref_known(v___y_1338_, 1);
                    v_snd_1345_ = crate::leanh::lean_ctor_get(v_val_1344_, 1);
                    crate::leanh::lean_inc(v_snd_1345_);
                    crate::leanh::lean_dec(v_val_1344_);
                    v_fst_1346_ = crate::leanh::lean_ctor_get(v_snd_1345_, 0);
                    crate::leanh::lean_inc(v_fst_1346_);
                    crate::leanh::lean_dec(v_snd_1345_);
                    v___x_1347_ = 0;
                    v___x_1348_ = l_Lean_Meta_DiscrTree_mkPath(
                        v_fst_1346_,
                        v___x_1347_,
                        v___x_1343_,
                        v_a_1276_,
                        v_a_1277_,
                        v_a_1278_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_1343_, 7);
                    return v___x_1348_;
                } else {
                    crate::leanh::lean_dec(v___y_1338_);
                    v___x_1349_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__2;
                    v___x_1350_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1351_ = l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1349_, v___x_1350_);
                    if v___x_1351_ == 0 {
                        v___x_1352_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__4;
                        v___x_1353_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1354_ = l_Lean_Expr_isAppOfArity(v_a_1336_, v___x_1352_, v___x_1353_);
                        if v___x_1354_ == 0 {
                            v___x_1355_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey___closed__6;
                            v___x_1356_ = crate::leanh::lean_unsigned_to_nat(1);
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
                                crate::leanh::lean_dec_ref_known(v___x_1343_, 7);
                                return v___x_1358_;
                            } else {
                                v___x_1359_ = l_Lean_Expr_appArg_x21(v_a_1336_);
                                crate::leanh::lean_dec(v_a_1336_);
                                v___x_1360_ = l_Lean_Meta_DiscrTree_mkPath(
                                    v___x_1359_,
                                    v___x_1354_,
                                    v___x_1343_,
                                    v_a_1276_,
                                    v_a_1277_,
                                    v_a_1278_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_1343_, 7);
                                return v___x_1360_;
                            }
                        } else {
                            v___x_1361_ = l_Lean_Expr_appFn_x21(v_a_1336_);
                            v___x_1362_ = l_Lean_Expr_appArg_x21(v___x_1361_);
                            crate::leanh::lean_dec_ref(v___x_1361_);
                            v___x_1363_ = l_Lean_Expr_appArg_x21(v_a_1336_);
                            crate::leanh::lean_dec(v_a_1336_);
                            v___x_1364_ = l_Lean_Meta_mkEq(
                                v___x_1362_,
                                v___x_1363_,
                                v___x_1343_,
                                v_a_1276_,
                                v_a_1277_,
                                v_a_1278_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1364_) == 0 {
                                v_a_1365_ = crate::leanh::lean_ctor_get(v___x_1364_, 0);
                                crate::leanh::lean_inc(v_a_1365_);
                                crate::leanh::lean_dec_ref_known(v___x_1364_, 1);
                                v___x_1366_ = l_Lean_Meta_DiscrTree_mkPath(
                                    v_a_1365_,
                                    v___x_1351_,
                                    v___x_1343_,
                                    v_a_1276_,
                                    v_a_1277_,
                                    v_a_1278_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_1343_, 7);
                                return v___x_1366_;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_1343_, 7);
                                v_a_1367_ = crate::leanh::lean_ctor_get(v___x_1364_, 0);
                                v_isSharedCheck_1374_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1364_)) as u8;
                                if v_isSharedCheck_1374_ == 0 {
                                    v___x_1369_ = v___x_1364_;
                                    v_isShared_1370_ = v_isSharedCheck_1374_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1367_);
                                    crate::leanh::lean_dec(v___x_1364_);
                                    v___x_1369_ = crate::leanh::lean_box(0);
                                    v_isShared_1370_ = v_isSharedCheck_1374_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v___x_1375_ = l_Lean_Expr_appFn_x21(v_a_1336_);
                        crate::leanh::lean_dec(v_a_1336_);
                        v___x_1376_ = l_Lean_Expr_appArg_x21(v___x_1375_);
                        crate::leanh::lean_dec_ref(v___x_1375_);
                        v___x_1377_ = 0;
                        v___x_1378_ = l_Lean_Meta_DiscrTree_mkPath(
                            v___x_1376_,
                            v___x_1377_,
                            v___x_1343_,
                            v_a_1276_,
                            v_a_1277_,
                            v_a_1278_,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_1343_, 7);
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
                    v_reuseFailAlloc_1373_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
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
                    crate::leanh::lean_ctor_set(v___x_1329_, 1, v___x_1389_);
                    crate::leanh::lean_ctor_set(v___x_1329_, 0, v___x_1385_);
                    v___x_1391_ = v___x_1329_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1393_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1393_, 1, v___x_1389_);
                    v___x_1391_ = v_reuseFailAlloc_1393_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1392_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1392_, 0, v___x_1391_);
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
                    v_reuseFailAlloc_1401_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_a_1395_);
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
                    v_reuseFailAlloc_1413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
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
    mut v_e_1417_: *mut crate::leanh::LeanObject,
    mut v_simp_1418_: *mut crate::leanh::LeanObject,
    mut v_a_1419_: *mut crate::leanh::LeanObject,
    mut v_a_1420_: *mut crate::leanh::LeanObject,
    mut v_a_1421_: *mut crate::leanh::LeanObject,
    mut v_a_1422_: *mut crate::leanh::LeanObject,
    mut v_a_1423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_simp_boxed_1424_: u8 = 0;
    let mut v_res_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_simp_boxed_1424_ = (crate::leanh::lean_unbox(v_simp_1418_) as u8);
    v_res_1425_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(
        v_e_1417_,
        v_simp_boxed_1424_,
        v_a_1419_,
        v_a_1420_,
        v_a_1421_,
        v_a_1422_,
    );
    crate::leanh::lean_dec(v_a_1422_);
    crate::leanh::lean_dec_ref(v_a_1421_);
    crate::leanh::lean_dec(v_a_1420_);
    crate::leanh::lean_dec_ref(v_a_1419_);
    return v_res_1425_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(
    mut v_msgData_1426_: *mut crate::leanh::LeanObject,
    mut v___y_1427_: *mut crate::leanh::LeanObject,
    mut v___y_1428_: *mut crate::leanh::LeanObject,
    mut v___y_1429_: *mut crate::leanh::LeanObject,
    mut v___y_1430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1432_ = lean_st_ref_get(v___y_1430_);
    v_env_1433_ = crate::leanh::lean_ctor_get(v___x_1432_, 0);
    crate::leanh::lean_inc_ref(v_env_1433_);
    crate::leanh::lean_dec(v___x_1432_);
    v___x_1434_ = lean_st_ref_get(v___y_1428_);
    v_mctx_1435_ = crate::leanh::lean_ctor_get(v___x_1434_, 0);
    crate::leanh::lean_inc_ref(v_mctx_1435_);
    crate::leanh::lean_dec(v___x_1434_);
    v_lctx_1436_ = crate::leanh::lean_ctor_get(v___y_1427_, 2);
    v_options_1437_ = crate::leanh::lean_ctor_get(v___y_1429_, 2);
    crate::leanh::lean_inc_ref(v_options_1437_);
    crate::leanh::lean_inc_ref(v_lctx_1436_);
    v___x_1438_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1438_, 0, v_env_1433_);
    crate::leanh::lean_ctor_set(v___x_1438_, 1, v_mctx_1435_);
    crate::leanh::lean_ctor_set(v___x_1438_, 2, v_lctx_1436_);
    crate::leanh::lean_ctor_set(v___x_1438_, 3, v_options_1437_);
    v___x_1439_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1439_, 0, v___x_1438_);
    crate::leanh::lean_ctor_set(v___x_1439_, 1, v_msgData_1426_);
    v___x_1440_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1440_, 0, v___x_1439_);
    return v___x_1440_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7___boxed(
    mut v_msgData_1441_: *mut crate::leanh::LeanObject,
    mut v___y_1442_: *mut crate::leanh::LeanObject,
    mut v___y_1443_: *mut crate::leanh::LeanObject,
    mut v___y_1444_: *mut crate::leanh::LeanObject,
    mut v___y_1445_: *mut crate::leanh::LeanObject,
    mut v___y_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msgData_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
    crate::leanh::lean_dec(v___y_1445_);
    crate::leanh::lean_dec_ref(v___y_1444_);
    crate::leanh::lean_dec(v___y_1443_);
    crate::leanh::lean_dec_ref(v___y_1442_);
    return v_res_1447_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(
    mut v_opts_1448_: *mut crate::leanh::LeanObject,
    mut v_opt_1449_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1450_ = crate::leanh::lean_ctor_get(v_opt_1449_, 0);
    v_defValue_1451_ = crate::leanh::lean_ctor_get(v_opt_1449_, 1);
    v_map_1452_ = crate::leanh::lean_ctor_get(v_opts_1448_, 0);
    v___x_1453_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1452_,
            v_name_1450_,
        );
    if crate::leanh::lean_obj_tag(v___x_1453_) == 0 {
        let mut v___x_1454_: u8 = 0;
        v___x_1454_ = (crate::leanh::lean_unbox(v_defValue_1451_) as u8);
        return v___x_1454_;
    } else {
        let mut v_val_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1455_ = crate::leanh::lean_ctor_get(v___x_1453_, 0);
        crate::leanh::lean_inc(v_val_1455_);
        crate::leanh::lean_dec_ref_known(v___x_1453_, 1);
        if crate::leanh::lean_obj_tag(v_val_1455_) == 1 {
            let mut v_v_1456_: u8 = 0;
            v_v_1456_ = crate::leanh::lean_ctor_get_uint8(v_val_1455_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1455_, 0);
            return v_v_1456_;
        } else {
            let mut v___x_1457_: u8 = 0;
            crate::leanh::lean_dec(v_val_1455_);
            v___x_1457_ = (crate::leanh::lean_unbox(v_defValue_1451_) as u8);
            return v___x_1457_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9___boxed(
    mut v_opts_1458_: *mut crate::leanh::LeanObject,
    mut v_opt_1459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1460_: u8 = 0;
    let mut v_r_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1460_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_opts_1458_, v_opt_1459_);
    crate::leanh::lean_dec_ref(v_opt_1459_);
    crate::leanh::lean_dec_ref(v_opts_1458_);
    v_r_1461_ = crate::leanh::lean_box((v_res_1460_) as usize);
    return v_r_1461_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = crate::leanh::lean_box(1);
    v___x_1463_ = l_Lean_MessageData_ofFormat(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__2;
    v___x_1468_ = l_Lean_MessageData_ofFormat(v___x_1467_);
    return v___x_1468_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(
    mut v_x_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v_before_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1492_: u8 = 0;
    let mut v_unused_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1494_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1470_) == 0 {
                    return v_x_1469_;
                } else {
                    v_head_1471_ = crate::leanh::lean_ctor_get(v_x_1470_, 0);
                    v_tail_1472_ = crate::leanh::lean_ctor_get(v_x_1470_, 1);
                    v_isSharedCheck_1494_ = (!crate::leanh::lean_is_exclusive(v_x_1470_)) as u8;
                    if v_isSharedCheck_1494_ == 0 {
                        v___x_1474_ = v_x_1470_;
                        v_isShared_1475_ = v_isSharedCheck_1494_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1472_);
                        crate::leanh::lean_inc(v_head_1471_);
                        crate::leanh::lean_dec(v_x_1470_);
                        v___x_1474_ = crate::leanh::lean_box(0);
                        v_isShared_1475_ = v_isSharedCheck_1494_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1476_ = crate::leanh::lean_ctor_get(v_head_1471_, 0);
                v_isSharedCheck_1492_ = (!crate::leanh::lean_is_exclusive(v_head_1471_)) as u8;
                if v_isSharedCheck_1492_ == 0 {
                    v_unused_1493_ = crate::leanh::lean_ctor_get(v_head_1471_, 1);
                    crate::leanh::lean_dec(v_unused_1493_);
                    v___x_1478_ = v_head_1471_;
                    v_isShared_1479_ = v_isSharedCheck_1492_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1476_);
                    crate::leanh::lean_dec(v_head_1471_);
                    v___x_1478_ = crate::leanh::lean_box(0);
                    v_isShared_1479_ = v_isSharedCheck_1492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1480_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0);
                if v_isShared_1479_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1478_, 7);
                    crate::leanh::lean_ctor_set(v___x_1478_, 1, v___x_1480_);
                    crate::leanh::lean_ctor_set(v___x_1478_, 0, v_x_1469_);
                    v___x_1482_ = v___x_1478_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1491_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_x_1469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1491_, 1, v___x_1480_);
                    v___x_1482_ = v_reuseFailAlloc_1491_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1483_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__3);
                if v_isShared_1475_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1474_, 7);
                    crate::leanh::lean_ctor_set(v___x_1474_, 1, v___x_1483_);
                    crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1482_);
                    v___x_1485_ = v___x_1474_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1490_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1490_, 1, v___x_1483_);
                    v___x_1485_ = v_reuseFailAlloc_1490_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1486_ = l_Lean_MessageData_ofSyntax(v_before_1476_);
                v___x_1487_ = l_Lean_indentD(v___x_1486_);
                v___x_1488_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1488_, 0, v___x_1485_);
                crate::leanh::lean_ctor_set(v___x_1488_, 1, v___x_1487_);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1498_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__1;
    v___x_1499_ = l_Lean_MessageData_ofFormat(v___x_1498_);
    return v___x_1499_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(
    mut v_msgData_1500_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1501_: *mut crate::leanh::LeanObject,
    mut v___y_1502_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1513_: u8 = 0;
    let mut v___x_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1525_: u8 = 0;
    let mut v_unused_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_1504_ = crate::leanh::lean_ctor_get(v___y_1502_, 2);
                v___x_1505_ = l_Lean_Elab_pp_macroStack;
                v___x_1506_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__9(v_options_1504_, v___x_1505_);
                if v___x_1506_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1501_);
                    v___x_1507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1507_, 0, v_msgData_1500_);
                    return v___x_1507_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1501_) == 0 {
                        v___x_1508_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1508_, 0, v_msgData_1500_);
                        return v___x_1508_;
                    } else {
                        v_head_1509_ = crate::leanh::lean_ctor_get(v_macroStack_1501_, 0);
                        crate::leanh::lean_inc(v_head_1509_);
                        v_after_1510_ = crate::leanh::lean_ctor_get(v_head_1509_, 1);
                        v_isSharedCheck_1525_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1509_)) as u8;
                        if v_isSharedCheck_1525_ == 0 {
                            v_unused_1526_ = crate::leanh::lean_ctor_get(v_head_1509_, 0);
                            crate::leanh::lean_dec(v_unused_1526_);
                            v___x_1512_ = v_head_1509_;
                            v_isShared_1513_ = v_isSharedCheck_1525_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1510_);
                            crate::leanh::lean_dec(v_head_1509_);
                            v___x_1512_ = crate::leanh::lean_box(0);
                            v_isShared_1513_ = v_isSharedCheck_1525_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1514_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10___closed__0);
                if v_isShared_1513_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1512_, 7);
                    crate::leanh::lean_ctor_set(v___x_1512_, 1, v___x_1514_);
                    crate::leanh::lean_ctor_set(v___x_1512_, 0, v_msgData_1500_);
                    v___x_1516_ = v___x_1512_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1524_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_msgData_1500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1524_, 1, v___x_1514_);
                    v___x_1516_ = v_reuseFailAlloc_1524_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1517_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___closed__2);
                v___x_1518_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1518_, 0, v___x_1516_);
                crate::leanh::lean_ctor_set(v___x_1518_, 1, v___x_1517_);
                v___x_1519_ = l_Lean_MessageData_ofSyntax(v_after_1510_);
                v___x_1520_ = l_Lean_indentD(v___x_1519_);
                v_msgData_1521_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1521_, 0, v___x_1518_);
                crate::leanh::lean_ctor_set(v_msgData_1521_, 1, v___x_1520_);
                v___x_1522_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8_spec__10(v_msgData_1521_, v_macroStack_1501_);
                v___x_1523_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1523_, 0, v___x_1522_);
                return v___x_1523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg___boxed(
    mut v_msgData_1527_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1528_: *mut crate::leanh::LeanObject,
    mut v___y_1529_: *mut crate::leanh::LeanObject,
    mut v___y_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1531_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msgData_1527_, v_macroStack_1528_, v___y_1529_);
    crate::leanh::lean_dec_ref(v___y_1529_);
    return v_res_1531_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(
    mut v_msg_1532_: *mut crate::leanh::LeanObject,
    mut v___y_1533_: *mut crate::leanh::LeanObject,
    mut v___y_1534_: *mut crate::leanh::LeanObject,
    mut v___y_1535_: *mut crate::leanh::LeanObject,
    mut v___y_1536_: *mut crate::leanh::LeanObject,
    mut v___y_1537_: *mut crate::leanh::LeanObject,
    mut v___y_1538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1554_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1540_ = crate::leanh::lean_ctor_get(v___y_1537_, 5);
                v___x_1541_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v_msg_1532_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
                v_a_1542_ = crate::leanh::lean_ctor_get(v___x_1541_, 0);
                crate::leanh::lean_inc(v_a_1542_);
                crate::leanh::lean_dec_ref(v___x_1541_);
                v_macroStack_1543_ = crate::leanh::lean_ctor_get(v___y_1533_, 1);
                v___x_1544_ = l_Lean_Elab_getBetterRef(v_ref_1540_, v_macroStack_1543_);
                crate::leanh::lean_inc(v_macroStack_1543_);
                v___x_1545_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_a_1542_, v_macroStack_1543_, v___y_1537_);
                v_a_1546_ = crate::leanh::lean_ctor_get(v___x_1545_, 0);
                v_isSharedCheck_1554_ = (!crate::leanh::lean_is_exclusive(v___x_1545_)) as u8;
                if v_isSharedCheck_1554_ == 0 {
                    v___x_1548_ = v___x_1545_;
                    v_isShared_1549_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1546_);
                    crate::leanh::lean_dec(v___x_1545_);
                    v___x_1548_ = crate::leanh::lean_box(0);
                    v_isShared_1549_ = v_isSharedCheck_1554_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1550_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1550_, 0, v___x_1544_);
                crate::leanh::lean_ctor_set(v___x_1550_, 1, v_a_1546_);
                if v_isShared_1549_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1548_, 1);
                    crate::leanh::lean_ctor_set(v___x_1548_, 0, v___x_1550_);
                    v___x_1552_ = v___x_1548_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1553_, 0, v___x_1550_);
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
    mut v_msg_1555_: *mut crate::leanh::LeanObject,
    mut v___y_1556_: *mut crate::leanh::LeanObject,
    mut v___y_1557_: *mut crate::leanh::LeanObject,
    mut v___y_1558_: *mut crate::leanh::LeanObject,
    mut v___y_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
    mut v___y_1561_: *mut crate::leanh::LeanObject,
    mut v___y_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
    crate::leanh::lean_dec(v___y_1561_);
    crate::leanh::lean_dec_ref(v___y_1560_);
    crate::leanh::lean_dec(v___y_1559_);
    crate::leanh::lean_dec_ref(v___y_1558_);
    crate::leanh::lean_dec(v___y_1557_);
    crate::leanh::lean_dec_ref(v___y_1556_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(
    mut v_ref_1564_: *mut crate::leanh::LeanObject,
    mut v_msg_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
    mut v___y_1567_: *mut crate::leanh::LeanObject,
    mut v___y_1568_: *mut crate::leanh::LeanObject,
    mut v___y_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1585_: u8 = 0;
    let mut v_cancelTk_x3f_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1587_: u8 = 0;
    let mut v_inheritedTraceOptions_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1573_ = crate::leanh::lean_ctor_get(v___y_1570_, 0);
    v_fileMap_1574_ = crate::leanh::lean_ctor_get(v___y_1570_, 1);
    v_options_1575_ = crate::leanh::lean_ctor_get(v___y_1570_, 2);
    v_currRecDepth_1576_ = crate::leanh::lean_ctor_get(v___y_1570_, 3);
    v_maxRecDepth_1577_ = crate::leanh::lean_ctor_get(v___y_1570_, 4);
    v_ref_1578_ = crate::leanh::lean_ctor_get(v___y_1570_, 5);
    v_currNamespace_1579_ = crate::leanh::lean_ctor_get(v___y_1570_, 6);
    v_openDecls_1580_ = crate::leanh::lean_ctor_get(v___y_1570_, 7);
    v_initHeartbeats_1581_ = crate::leanh::lean_ctor_get(v___y_1570_, 8);
    v_maxHeartbeats_1582_ = crate::leanh::lean_ctor_get(v___y_1570_, 9);
    v_quotContext_1583_ = crate::leanh::lean_ctor_get(v___y_1570_, 10);
    v_currMacroScope_1584_ = crate::leanh::lean_ctor_get(v___y_1570_, 11);
    v_diag_1585_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1570_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1586_ = crate::leanh::lean_ctor_get(v___y_1570_, 12);
    v_suppressElabErrors_1587_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1570_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1588_ = crate::leanh::lean_ctor_get(v___y_1570_, 13);
    v_ref_1589_ = l_Lean_replaceRef(v_ref_1564_, v_ref_1578_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1588_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1586_);
    crate::leanh::lean_inc(v_currMacroScope_1584_);
    crate::leanh::lean_inc(v_quotContext_1583_);
    crate::leanh::lean_inc(v_maxHeartbeats_1582_);
    crate::leanh::lean_inc(v_initHeartbeats_1581_);
    crate::leanh::lean_inc(v_openDecls_1580_);
    crate::leanh::lean_inc(v_currNamespace_1579_);
    crate::leanh::lean_inc(v_maxRecDepth_1577_);
    crate::leanh::lean_inc(v_currRecDepth_1576_);
    crate::leanh::lean_inc_ref(v_options_1575_);
    crate::leanh::lean_inc_ref(v_fileMap_1574_);
    crate::leanh::lean_inc_ref(v_fileName_1573_);
    v___x_1590_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1590_, 0, v_fileName_1573_);
    crate::leanh::lean_ctor_set(v___x_1590_, 1, v_fileMap_1574_);
    crate::leanh::lean_ctor_set(v___x_1590_, 2, v_options_1575_);
    crate::leanh::lean_ctor_set(v___x_1590_, 3, v_currRecDepth_1576_);
    crate::leanh::lean_ctor_set(v___x_1590_, 4, v_maxRecDepth_1577_);
    crate::leanh::lean_ctor_set(v___x_1590_, 5, v_ref_1589_);
    crate::leanh::lean_ctor_set(v___x_1590_, 6, v_currNamespace_1579_);
    crate::leanh::lean_ctor_set(v___x_1590_, 7, v_openDecls_1580_);
    crate::leanh::lean_ctor_set(v___x_1590_, 8, v_initHeartbeats_1581_);
    crate::leanh::lean_ctor_set(v___x_1590_, 9, v_maxHeartbeats_1582_);
    crate::leanh::lean_ctor_set(v___x_1590_, 10, v_quotContext_1583_);
    crate::leanh::lean_ctor_set(v___x_1590_, 11, v_currMacroScope_1584_);
    crate::leanh::lean_ctor_set(v___x_1590_, 12, v_cancelTk_x3f_1586_);
    crate::leanh::lean_ctor_set(v___x_1590_, 13, v_inheritedTraceOptions_1588_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1590_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1585_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1590_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1587_,
    );
    v___x_1591_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___x_1590_, v___y_1571_);
    crate::leanh::lean_dec_ref_known(v___x_1590_, 14);
    return v___x_1591_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg___boxed(
    mut v_ref_1592_: *mut crate::leanh::LeanObject,
    mut v_msg_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
    mut v___y_1596_: *mut crate::leanh::LeanObject,
    mut v___y_1597_: *mut crate::leanh::LeanObject,
    mut v___y_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1601_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1592_, v_msg_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
    crate::leanh::lean_dec(v___y_1599_);
    crate::leanh::lean_dec_ref(v___y_1598_);
    crate::leanh::lean_dec(v___y_1597_);
    crate::leanh::lean_dec_ref(v___y_1596_);
    crate::leanh::lean_dec(v___y_1595_);
    crate::leanh::lean_dec_ref(v___y_1594_);
    crate::leanh::lean_dec(v_ref_1592_);
    return v_res_1601_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1602_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1603_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_1604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1603_);
    return v___x_1604_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1606_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1607_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1607_, 0, v___x_1606_);
    crate::leanh::lean_ctor_set(v___x_1607_, 1, v___x_1606_);
    crate::leanh::lean_ctor_set(v___x_1607_, 2, v___x_1606_);
    crate::leanh::lean_ctor_set(v___x_1607_, 3, v___x_1606_);
    crate::leanh::lean_ctor_set(v___x_1607_, 4, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1607_, 5, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1607_, 6, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1607_, 7, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1607_, 8, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1607_, 9, v___x_1605_);
    return v___x_1607_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1608_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1609_ = lean_mk_empty_array_with_capacity(v___x_1608_);
    v___x_1610_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    return v___x_1610_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1611_: usize = 0;
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1611_ = 5usize;
    v___x_1612_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1613_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1614_ = lean_mk_empty_array_with_capacity(v___x_1613_);
    v___x_1615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__3);
    v___x_1616_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1616_, 0, v___x_1615_);
    crate::leanh::lean_ctor_set(v___x_1616_, 1, v___x_1614_);
    crate::leanh::lean_ctor_set(v___x_1616_, 2, v___x_1612_);
    crate::leanh::lean_ctor_set(v___x_1616_, 3, v___x_1612_);
    crate::leanh::lean_ctor_set_usize(v___x_1616_, 4, v___x_1611_);
    return v___x_1616_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = crate::leanh::lean_box(1);
    v___x_1618_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__4);
    v___x_1619_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__1);
    v___x_1620_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1620_, 0, v___x_1619_);
    crate::leanh::lean_ctor_set(v___x_1620_, 1, v___x_1618_);
    crate::leanh::lean_ctor_set(v___x_1620_, 2, v___x_1617_);
    return v___x_1620_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1622_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__6;
    v___x_1623_ = l_Lean_stringToMessageData(v___x_1622_);
    return v___x_1623_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1625_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__8;
    v___x_1626_ = l_Lean_stringToMessageData(v___x_1625_);
    return v___x_1626_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1628_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__10;
    v___x_1629_ = l_Lean_stringToMessageData(v___x_1628_);
    return v___x_1629_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__12;
    v___x_1632_ = l_Lean_stringToMessageData(v___x_1631_);
    return v___x_1632_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1634_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__14;
    v___x_1635_ = l_Lean_stringToMessageData(v___x_1634_);
    return v___x_1635_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1637_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__16;
    v___x_1638_ = l_Lean_stringToMessageData(v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__18;
    v___x_1641_ = l_Lean_stringToMessageData(v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_msg_1642_: *mut crate::leanh::LeanObject,
    mut v_declHint_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: u8 = 0;
    let mut v_isExporting_1649_: u8 = 0;
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1652_: u8 = 0;
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1646_ = lean_st_ref_get(v___y_1644_);
                v_env_1647_ = crate::leanh::lean_ctor_get(v___x_1646_, 0);
                crate::leanh::lean_inc_ref(v_env_1647_);
                crate::leanh::lean_dec(v___x_1646_);
                v___x_1648_ = l_Lean_Name_isAnonymous(v_declHint_1643_);
                if v___x_1648_ == 0 {
                    v_isExporting_1649_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1647_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1649_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1647_);
                        crate::leanh::lean_dec(v_declHint_1643_);
                        v___x_1650_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1650_, 0, v_msg_1642_);
                        return v___x_1650_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1647_);
                        v___x_1651_ = l_Lean_Environment_setExporting(v_env_1647_, v___x_1648_);
                        crate::leanh::lean_inc(v_declHint_1643_);
                        crate::leanh::lean_inc_ref(v___x_1651_);
                        v___x_1652_ = l_Lean_Environment_contains(
                            v___x_1651_,
                            v_declHint_1643_,
                            v_isExporting_1649_,
                        );
                        if v___x_1652_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1651_);
                            crate::leanh::lean_dec_ref(v_env_1647_);
                            crate::leanh::lean_dec(v_declHint_1643_);
                            v___x_1653_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1653_, 0, v_msg_1642_);
                            return v___x_1653_;
                        } else {
                            v___x_1654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__2);
                            v___x_1655_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__5);
                            v___x_1656_ = l_Lean_Options_empty;
                            v___x_1657_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1651_);
                            crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1654_);
                            crate::leanh::lean_ctor_set(v___x_1657_, 2, v___x_1655_);
                            crate::leanh::lean_ctor_set(v___x_1657_, 3, v___x_1656_);
                            crate::leanh::lean_inc(v_declHint_1643_);
                            v___x_1658_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1643_, v___x_1648_);
                            v_c_1659_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1659_, 0, v___x_1657_);
                            crate::leanh::lean_ctor_set(v_c_1659_, 1, v___x_1658_);
                            v___x_1660_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1647_,
                                v_declHint_1643_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1660_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1647_);
                                crate::leanh::lean_dec(v_declHint_1643_);
                                v___x_1661_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                                v___x_1662_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1662_, 0, v___x_1661_);
                                crate::leanh::lean_ctor_set(v___x_1662_, 1, v_c_1659_);
                                v___x_1663_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__9);
                                v___x_1664_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1664_, 0, v___x_1662_);
                                crate::leanh::lean_ctor_set(v___x_1664_, 1, v___x_1663_);
                                v___x_1665_ = l_Lean_MessageData_note(v___x_1664_);
                                v___x_1666_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1666_, 0, v_msg_1642_);
                                crate::leanh::lean_ctor_set(v___x_1666_, 1, v___x_1665_);
                                v___x_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1666_);
                                return v___x_1667_;
                            } else {
                                v_val_1668_ = crate::leanh::lean_ctor_get(v___x_1660_, 0);
                                v_isSharedCheck_1703_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1660_)) as u8;
                                if v_isSharedCheck_1703_ == 0 {
                                    v___x_1670_ = v___x_1660_;
                                    v_isShared_1671_ = v_isSharedCheck_1703_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1668_);
                                    crate::leanh::lean_dec(v___x_1660_);
                                    v___x_1670_ = crate::leanh::lean_box(0);
                                    v_isShared_1671_ = v_isSharedCheck_1703_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1647_);
                    crate::leanh::lean_dec(v_declHint_1643_);
                    v___x_1704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1704_, 0, v_msg_1642_);
                    return v___x_1704_;
                }
            }
            1 => {
                v___x_1672_ = crate::leanh::lean_box(0);
                v___x_1673_ = l_Lean_Environment_header(v_env_1647_);
                crate::leanh::lean_dec_ref(v_env_1647_);
                v___x_1674_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1673_);
                v_mod_1675_ = lean_array_get(v___x_1672_, v___x_1674_, v_val_1668_);
                crate::leanh::lean_dec(v_val_1668_);
                crate::leanh::lean_dec_ref(v___x_1674_);
                v___x_1676_ = l_Lean_isPrivateName(v_declHint_1643_);
                crate::leanh::lean_dec(v_declHint_1643_);
                if v___x_1676_ == 0 {
                    v___x_1677_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__11);
                    v___x_1678_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1678_, 0, v___x_1677_);
                    crate::leanh::lean_ctor_set(v___x_1678_, 1, v_c_1659_);
                    v___x_1679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__13);
                    v___x_1680_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1680_, 0, v___x_1678_);
                    crate::leanh::lean_ctor_set(v___x_1680_, 1, v___x_1679_);
                    v___x_1681_ = l_Lean_MessageData_ofName(v_mod_1675_);
                    v___x_1682_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1682_, 0, v___x_1680_);
                    crate::leanh::lean_ctor_set(v___x_1682_, 1, v___x_1681_);
                    v___x_1683_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__15);
                    v___x_1684_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1684_, 0, v___x_1682_);
                    crate::leanh::lean_ctor_set(v___x_1684_, 1, v___x_1683_);
                    v___x_1685_ = l_Lean_MessageData_note(v___x_1684_);
                    v___x_1686_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1686_, 0, v_msg_1642_);
                    crate::leanh::lean_ctor_set(v___x_1686_, 1, v___x_1685_);
                    if v_isShared_1671_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1670_, 0);
                        crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1686_);
                        v___x_1688_ = v___x_1670_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1686_);
                        v___x_1688_ = v_reuseFailAlloc_1689_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1690_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__7);
                    v___x_1691_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1691_, 0, v___x_1690_);
                    crate::leanh::lean_ctor_set(v___x_1691_, 1, v_c_1659_);
                    v___x_1692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__17);
                    v___x_1693_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v___x_1691_);
                    crate::leanh::lean_ctor_set(v___x_1693_, 1, v___x_1692_);
                    v___x_1694_ = l_Lean_MessageData_ofName(v_mod_1675_);
                    v___x_1695_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1695_, 0, v___x_1693_);
                    crate::leanh::lean_ctor_set(v___x_1695_, 1, v___x_1694_);
                    v___x_1696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg___closed__19);
                    v___x_1697_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1697_, 0, v___x_1695_);
                    crate::leanh::lean_ctor_set(v___x_1697_, 1, v___x_1696_);
                    v___x_1698_ = l_Lean_MessageData_note(v___x_1697_);
                    v___x_1699_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1699_, 0, v_msg_1642_);
                    crate::leanh::lean_ctor_set(v___x_1699_, 1, v___x_1698_);
                    if v_isShared_1671_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1670_, 0);
                        crate::leanh::lean_ctor_set(v___x_1670_, 0, v___x_1699_);
                        v___x_1701_ = v___x_1670_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
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
    mut v_msg_1705_: *mut crate::leanh::LeanObject,
    mut v_declHint_1706_: *mut crate::leanh::LeanObject,
    mut v___y_1707_: *mut crate::leanh::LeanObject,
    mut v___y_1708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1709_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1705_, v_declHint_1706_, v___y_1707_);
    crate::leanh::lean_dec(v___y_1707_);
    return v_res_1709_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3(
    mut v_msg_1710_: *mut crate::leanh::LeanObject,
    mut v_declHint_1711_: *mut crate::leanh::LeanObject,
    mut v___y_1712_: *mut crate::leanh::LeanObject,
    mut v___y_1713_: *mut crate::leanh::LeanObject,
    mut v___y_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1719_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1710_, v_declHint_1711_, v___y_1717_);
                v_a_1720_ = crate::leanh::lean_ctor_get(v___x_1719_, 0);
                v_isSharedCheck_1729_ = (!crate::leanh::lean_is_exclusive(v___x_1719_)) as u8;
                if v_isSharedCheck_1729_ == 0 {
                    v___x_1722_ = v___x_1719_;
                    v_isShared_1723_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1720_);
                    crate::leanh::lean_dec(v___x_1719_);
                    v___x_1722_ = crate::leanh::lean_box(0);
                    v_isShared_1723_ = v_isSharedCheck_1729_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1724_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1725_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
                crate::leanh::lean_ctor_set(v___x_1725_, 1, v_a_1720_);
                if v_isShared_1723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1722_, 0, v___x_1725_);
                    v___x_1727_ = v___x_1722_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1728_, 0, v___x_1725_);
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
    mut v_msg_1730_: *mut crate::leanh::LeanObject,
    mut v_declHint_1731_: *mut crate::leanh::LeanObject,
    mut v___y_1732_: *mut crate::leanh::LeanObject,
    mut v___y_1733_: *mut crate::leanh::LeanObject,
    mut v___y_1734_: *mut crate::leanh::LeanObject,
    mut v___y_1735_: *mut crate::leanh::LeanObject,
    mut v___y_1736_: *mut crate::leanh::LeanObject,
    mut v___y_1737_: *mut crate::leanh::LeanObject,
    mut v___y_1738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1739_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1730_, v_declHint_1731_, v___y_1732_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_, v___y_1737_);
    crate::leanh::lean_dec(v___y_1737_);
    crate::leanh::lean_dec_ref(v___y_1736_);
    crate::leanh::lean_dec(v___y_1735_);
    crate::leanh::lean_dec_ref(v___y_1734_);
    crate::leanh::lean_dec(v___y_1733_);
    crate::leanh::lean_dec_ref(v___y_1732_);
    return v_res_1739_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_ref_1740_: *mut crate::leanh::LeanObject,
    mut v_msg_1741_: *mut crate::leanh::LeanObject,
    mut v_declHint_1742_: *mut crate::leanh::LeanObject,
    mut v___y_1743_: *mut crate::leanh::LeanObject,
    mut v___y_1744_: *mut crate::leanh::LeanObject,
    mut v___y_1745_: *mut crate::leanh::LeanObject,
    mut v___y_1746_: *mut crate::leanh::LeanObject,
    mut v___y_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1750_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3(v_msg_1741_, v_declHint_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
    v_a_1751_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
    crate::leanh::lean_inc(v_a_1751_);
    crate::leanh::lean_dec_ref(v___x_1750_);
    v___x_1752_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1740_, v_a_1751_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
    return v___x_1752_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_ref_1753_: *mut crate::leanh::LeanObject,
    mut v_msg_1754_: *mut crate::leanh::LeanObject,
    mut v_declHint_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
    mut v___y_1761_: *mut crate::leanh::LeanObject,
    mut v___y_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1763_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1753_, v_msg_1754_, v_declHint_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_);
    crate::leanh::lean_dec(v___y_1761_);
    crate::leanh::lean_dec_ref(v___y_1760_);
    crate::leanh::lean_dec(v___y_1759_);
    crate::leanh::lean_dec_ref(v___y_1758_);
    crate::leanh::lean_dec(v___y_1757_);
    crate::leanh::lean_dec_ref(v___y_1756_);
    crate::leanh::lean_dec(v_ref_1753_);
    return v_res_1763_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1766_ = l_Lean_stringToMessageData(v___x_1765_);
    return v___x_1766_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1768_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1769_ = l_Lean_stringToMessageData(v___x_1768_);
    return v___x_1769_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1770_: *mut crate::leanh::LeanObject,
    mut v_constName_1771_: *mut crate::leanh::LeanObject,
    mut v___y_1772_: *mut crate::leanh::LeanObject,
    mut v___y_1773_: *mut crate::leanh::LeanObject,
    mut v___y_1774_: *mut crate::leanh::LeanObject,
    mut v___y_1775_: *mut crate::leanh::LeanObject,
    mut v___y_1776_: *mut crate::leanh::LeanObject,
    mut v___y_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: u8 = 0;
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1779_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1780_ = 0;
    crate::leanh::lean_inc(v_constName_1771_);
    v___x_1781_ = l_Lean_MessageData_ofConstName(v_constName_1771_, v___x_1780_);
    v___x_1782_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1782_, 0, v___x_1779_);
    crate::leanh::lean_ctor_set(v___x_1782_, 1, v___x_1781_);
    v___x_1783_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1784_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1784_, 0, v___x_1782_);
    crate::leanh::lean_ctor_set(v___x_1784_, 1, v___x_1783_);
    v___x_1785_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1770_, v___x_1784_, v_constName_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_, v___y_1777_);
    return v___x_1785_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1786_: *mut crate::leanh::LeanObject,
    mut v_constName_1787_: *mut crate::leanh::LeanObject,
    mut v___y_1788_: *mut crate::leanh::LeanObject,
    mut v___y_1789_: *mut crate::leanh::LeanObject,
    mut v___y_1790_: *mut crate::leanh::LeanObject,
    mut v___y_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1795_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(v_ref_1786_, v_constName_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
    crate::leanh::lean_dec(v___y_1793_);
    crate::leanh::lean_dec_ref(v___y_1792_);
    crate::leanh::lean_dec(v___y_1791_);
    crate::leanh::lean_dec_ref(v___y_1790_);
    crate::leanh::lean_dec(v___y_1789_);
    crate::leanh::lean_dec_ref(v___y_1788_);
    crate::leanh::lean_dec(v_ref_1786_);
    return v_res_1795_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(
    mut v_constName_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
    mut v___y_1801_: *mut crate::leanh::LeanObject,
    mut v___y_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1804_ = crate::leanh::lean_ctor_get(v___y_1801_, 5);
    v___x_1805_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(v_ref_1804_, v_constName_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
    return v___x_1805_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1806_: *mut crate::leanh::LeanObject,
    mut v___y_1807_: *mut crate::leanh::LeanObject,
    mut v___y_1808_: *mut crate::leanh::LeanObject,
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(v_constName_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
    crate::leanh::lean_dec(v___y_1812_);
    crate::leanh::lean_dec_ref(v___y_1811_);
    crate::leanh::lean_dec(v___y_1810_);
    crate::leanh::lean_dec_ref(v___y_1809_);
    crate::leanh::lean_dec(v___y_1808_);
    crate::leanh::lean_dec_ref(v___y_1807_);
    return v_res_1814_;
}
pub unsafe fn l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(
    mut v_constName_1815_: *mut crate::leanh::LeanObject,
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
    mut v___y_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1823_ = lean_st_ref_get(v___y_1821_);
                v_env_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                crate::leanh::lean_inc_ref(v_env_1824_);
                crate::leanh::lean_dec(v___x_1823_);
                v___x_1825_ = 0;
                crate::leanh::lean_inc(v_constName_1815_);
                v___x_1826_ =
                    l_Lean_Environment_find_x3f(v_env_1824_, v_constName_1815_, v___x_1825_);
                if crate::leanh::lean_obj_tag(v___x_1826_) == 0 {
                    v___x_1827_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(v_constName_1815_, v___y_1816_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
                    return v___x_1827_;
                } else {
                    crate::leanh::lean_dec(v_constName_1815_);
                    v_val_1828_ = crate::leanh::lean_ctor_get(v___x_1826_, 0);
                    v_isSharedCheck_1835_ = (!crate::leanh::lean_is_exclusive(v___x_1826_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1830_ = v___x_1826_;
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1828_);
                        crate::leanh::lean_dec(v___x_1826_);
                        v___x_1830_ = crate::leanh::lean_box(0);
                        v_isShared_1831_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1831_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1830_, 0);
                    v___x_1833_ = v___x_1830_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_val_1828_);
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
    mut v_constName_1836_: *mut crate::leanh::LeanObject,
    mut v___y_1837_: *mut crate::leanh::LeanObject,
    mut v___y_1838_: *mut crate::leanh::LeanObject,
    mut v___y_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(v_constName_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
    crate::leanh::lean_dec(v___y_1842_);
    crate::leanh::lean_dec_ref(v___y_1841_);
    crate::leanh::lean_dec(v___y_1840_);
    crate::leanh::lean_dec_ref(v___y_1839_);
    crate::leanh::lean_dec(v___y_1838_);
    crate::leanh::lean_dec_ref(v___y_1837_);
    return v_res_1844_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(
    mut v_t_1848_: *mut crate::leanh::LeanObject,
    mut v_a_1849_: *mut crate::leanh::LeanObject,
    mut v_a_1850_: *mut crate::leanh::LeanObject,
    mut v_a_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: u8 = 0;
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: u8 = 0;
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1867_: u8 = 0;
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1880_: u8 = 0;
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v_a_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_a_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1856_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType___closed__1;
                crate::leanh::lean_inc(v_t_1848_);
                v___x_1857_ = l_Lean_Syntax_isOfKind(v_t_1848_, v___x_1856_);
                if v___x_1857_ == 0 {
                    v___x_1858_ = crate::leanh::lean_box(0);
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
                    v_lctx_1861_ = crate::leanh::lean_ctor_get(v_a_1851_, 2);
                    v___x_1862_ = l_Lean_TSyntax_getId(v_t_1848_);
                    v___x_1863_ =
                        l_Lean_LocalContext_findFromUserName_x3f(v_lctx_1861_, v___x_1862_);
                    crate::leanh::lean_dec(v___x_1862_);
                    if crate::leanh::lean_obj_tag(v___x_1863_) == 1 {
                        crate::leanh::lean_dec(v_t_1848_);
                        v_val_1864_ = crate::leanh::lean_ctor_get(v___x_1863_, 0);
                        v_isSharedCheck_1872_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1863_)) as u8;
                        if v_isSharedCheck_1872_ == 0 {
                            v___x_1866_ = v___x_1863_;
                            v_isShared_1867_ = v_isSharedCheck_1872_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1864_);
                            crate::leanh::lean_dec(v___x_1863_);
                            v___x_1866_ = crate::leanh::lean_box(0);
                            v_isShared_1867_ = v_isSharedCheck_1872_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1863_);
                        v___x_1873_ = crate::leanh::lean_box(0);
                        v___x_1874_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                            v_t_1848_,
                            v___x_1873_,
                            v_a_1853_,
                            v_a_1854_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1874_) == 0 {
                            v_a_1875_ = crate::leanh::lean_ctor_get(v___x_1874_, 0);
                            crate::leanh::lean_inc(v_a_1875_);
                            crate::leanh::lean_dec_ref_known(v___x_1874_, 1);
                            v___x_1876_ = l_Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0(v_a_1875_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_);
                            if crate::leanh::lean_obj_tag(v___x_1876_) == 0 {
                                v_a_1877_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
                                v_isSharedCheck_1885_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1876_)) as u8;
                                if v_isSharedCheck_1885_ == 0 {
                                    v___x_1879_ = v___x_1876_;
                                    v_isShared_1880_ = v_isSharedCheck_1885_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1877_);
                                    crate::leanh::lean_dec(v___x_1876_);
                                    v___x_1879_ = crate::leanh::lean_box(0);
                                    v_isShared_1880_ = v_isSharedCheck_1885_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                v_a_1886_ = crate::leanh::lean_ctor_get(v___x_1876_, 0);
                                v_isSharedCheck_1893_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1876_)) as u8;
                                if v_isSharedCheck_1893_ == 0 {
                                    v___x_1888_ = v___x_1876_;
                                    v_isShared_1889_ = v_isSharedCheck_1893_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1886_);
                                    crate::leanh::lean_dec(v___x_1876_);
                                    v___x_1888_ = crate::leanh::lean_box(0);
                                    v_isShared_1889_ = v_isSharedCheck_1893_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            v_a_1894_ = crate::leanh::lean_ctor_get(v___x_1874_, 0);
                            v_isSharedCheck_1901_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1874_)) as u8;
                            if v_isSharedCheck_1901_ == 0 {
                                v___x_1896_ = v___x_1874_;
                                v_isShared_1897_ = v_isSharedCheck_1901_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1894_);
                                crate::leanh::lean_dec(v___x_1874_);
                                v___x_1896_ = crate::leanh::lean_box(0);
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
                crate::leanh::lean_dec(v_val_1864_);
                if v_isShared_1867_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1866_, 0);
                    crate::leanh::lean_ctor_set(v___x_1866_, 0, v___x_1868_);
                    v___x_1870_ = v___x_1866_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1871_, 0, v___x_1868_);
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
                crate::leanh::lean_dec(v_a_1877_);
                if v_isShared_1880_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1881_);
                    v___x_1883_ = v___x_1879_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
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
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
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
                    v_reuseFailAlloc_1900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
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
    mut v_t_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
    mut v_a_1904_: *mut crate::leanh::LeanObject,
    mut v_a_1905_: *mut crate::leanh::LeanObject,
    mut v_a_1906_: *mut crate::leanh::LeanObject,
    mut v_a_1907_: *mut crate::leanh::LeanObject,
    mut v_a_1908_: *mut crate::leanh::LeanObject,
    mut v_a_1909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1910_ =
        l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(
            v_t_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_, v_a_1907_, v_a_1908_,
        );
    crate::leanh::lean_dec(v_a_1908_);
    crate::leanh::lean_dec_ref(v_a_1907_);
    crate::leanh::lean_dec(v_a_1906_);
    crate::leanh::lean_dec_ref(v_a_1905_);
    crate::leanh::lean_dec(v_a_1904_);
    crate::leanh::lean_dec_ref(v_a_1903_);
    return v_res_1910_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0(
    mut v_00_u03b1_1911_: *mut crate::leanh::LeanObject,
    mut v_constName_1912_: *mut crate::leanh::LeanObject,
    mut v___y_1913_: *mut crate::leanh::LeanObject,
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v___y_1915_: *mut crate::leanh::LeanObject,
    mut v___y_1916_: *mut crate::leanh::LeanObject,
    mut v___y_1917_: *mut crate::leanh::LeanObject,
    mut v___y_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1920_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___redArg(v_constName_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_, v___y_1918_);
    return v___x_1920_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1921_: *mut crate::leanh::LeanObject,
    mut v_constName_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
    mut v___y_1928_: *mut crate::leanh::LeanObject,
    mut v___y_1929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0(v_00_u03b1_1921_, v_constName_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
    crate::leanh::lean_dec(v___y_1928_);
    crate::leanh::lean_dec_ref(v___y_1927_);
    crate::leanh::lean_dec(v___y_1926_);
    crate::leanh::lean_dec_ref(v___y_1925_);
    crate::leanh::lean_dec(v___y_1924_);
    crate::leanh::lean_dec_ref(v___y_1923_);
    return v_res_1930_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1931_: *mut crate::leanh::LeanObject,
    mut v_ref_1932_: *mut crate::leanh::LeanObject,
    mut v_constName_1933_: *mut crate::leanh::LeanObject,
    mut v___y_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
    mut v___y_1936_: *mut crate::leanh::LeanObject,
    mut v___y_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
    mut v___y_1939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___redArg(v_ref_1932_, v_constName_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
    return v___x_1941_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1942_: *mut crate::leanh::LeanObject,
    mut v_ref_1943_: *mut crate::leanh::LeanObject,
    mut v_constName_1944_: *mut crate::leanh::LeanObject,
    mut v___y_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
    mut v___y_1948_: *mut crate::leanh::LeanObject,
    mut v___y_1949_: *mut crate::leanh::LeanObject,
    mut v___y_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1(v_00_u03b1_1942_, v_ref_1943_, v_constName_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
    crate::leanh::lean_dec(v___y_1950_);
    crate::leanh::lean_dec_ref(v___y_1949_);
    crate::leanh::lean_dec(v___y_1948_);
    crate::leanh::lean_dec_ref(v___y_1947_);
    crate::leanh::lean_dec(v___y_1946_);
    crate::leanh::lean_dec_ref(v___y_1945_);
    crate::leanh::lean_dec(v_ref_1943_);
    return v_res_1952_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b1_1953_: *mut crate::leanh::LeanObject,
    mut v_ref_1954_: *mut crate::leanh::LeanObject,
    mut v_msg_1955_: *mut crate::leanh::LeanObject,
    mut v_declHint_1956_: *mut crate::leanh::LeanObject,
    mut v___y_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
    mut v___y_1960_: *mut crate::leanh::LeanObject,
    mut v___y_1961_: *mut crate::leanh::LeanObject,
    mut v___y_1962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1964_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___redArg(v_ref_1954_, v_msg_1955_, v_declHint_1956_, v___y_1957_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
    return v___x_1964_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b1_1965_: *mut crate::leanh::LeanObject,
    mut v_ref_1966_: *mut crate::leanh::LeanObject,
    mut v_msg_1967_: *mut crate::leanh::LeanObject,
    mut v_declHint_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
    mut v___y_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
    mut v___y_1975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2(v_00_u03b1_1965_, v_ref_1966_, v_msg_1967_, v_declHint_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_, v___y_1974_);
    crate::leanh::lean_dec(v___y_1974_);
    crate::leanh::lean_dec_ref(v___y_1973_);
    crate::leanh::lean_dec(v___y_1972_);
    crate::leanh::lean_dec_ref(v___y_1971_);
    crate::leanh::lean_dec(v___y_1970_);
    crate::leanh::lean_dec_ref(v___y_1969_);
    crate::leanh::lean_dec(v_ref_1966_);
    return v_res_1976_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(
    mut v_msg_1977_: *mut crate::leanh::LeanObject,
    mut v_declHint_1978_: *mut crate::leanh::LeanObject,
    mut v___y_1979_: *mut crate::leanh::LeanObject,
    mut v___y_1980_: *mut crate::leanh::LeanObject,
    mut v___y_1981_: *mut crate::leanh::LeanObject,
    mut v___y_1982_: *mut crate::leanh::LeanObject,
    mut v___y_1983_: *mut crate::leanh::LeanObject,
    mut v___y_1984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1986_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___redArg(v_msg_1977_, v_declHint_1978_, v___y_1984_);
    return v___x_1986_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4___boxed(
    mut v_msg_1987_: *mut crate::leanh::LeanObject,
    mut v_declHint_1988_: *mut crate::leanh::LeanObject,
    mut v___y_1989_: *mut crate::leanh::LeanObject,
    mut v___y_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
    mut v___y_1993_: *mut crate::leanh::LeanObject,
    mut v___y_1994_: *mut crate::leanh::LeanObject,
    mut v___y_1995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1996_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__3_spec__4(v_msg_1987_, v_declHint_1988_, v___y_1989_, v___y_1990_, v___y_1991_, v___y_1992_, v___y_1993_, v___y_1994_);
    crate::leanh::lean_dec(v___y_1994_);
    crate::leanh::lean_dec_ref(v___y_1993_);
    crate::leanh::lean_dec(v___y_1992_);
    crate::leanh::lean_dec_ref(v___y_1991_);
    crate::leanh::lean_dec(v___y_1990_);
    crate::leanh::lean_dec_ref(v___y_1989_);
    return v_res_1996_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4(
    mut v_00_u03b1_1997_: *mut crate::leanh::LeanObject,
    mut v_ref_1998_: *mut crate::leanh::LeanObject,
    mut v_msg_1999_: *mut crate::leanh::LeanObject,
    mut v___y_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
    mut v___y_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___redArg(v_ref_1998_, v_msg_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_, v___y_2004_, v___y_2005_);
    return v___x_2007_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4___boxed(
    mut v_00_u03b1_2008_: *mut crate::leanh::LeanObject,
    mut v_ref_2009_: *mut crate::leanh::LeanObject,
    mut v_msg_2010_: *mut crate::leanh::LeanObject,
    mut v___y_2011_: *mut crate::leanh::LeanObject,
    mut v___y_2012_: *mut crate::leanh::LeanObject,
    mut v___y_2013_: *mut crate::leanh::LeanObject,
    mut v___y_2014_: *mut crate::leanh::LeanObject,
    mut v___y_2015_: *mut crate::leanh::LeanObject,
    mut v___y_2016_: *mut crate::leanh::LeanObject,
    mut v___y_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4(v_00_u03b1_2008_, v_ref_2009_, v_msg_2010_, v___y_2011_, v___y_2012_, v___y_2013_, v___y_2014_, v___y_2015_, v___y_2016_);
    crate::leanh::lean_dec(v___y_2016_);
    crate::leanh::lean_dec_ref(v___y_2015_);
    crate::leanh::lean_dec(v___y_2014_);
    crate::leanh::lean_dec_ref(v___y_2013_);
    crate::leanh::lean_dec(v___y_2012_);
    crate::leanh::lean_dec_ref(v___y_2011_);
    crate::leanh::lean_dec(v_ref_2009_);
    return v_res_2018_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(
    mut v_00_u03b1_2019_: *mut crate::leanh::LeanObject,
    mut v_msg_2020_: *mut crate::leanh::LeanObject,
    mut v___y_2021_: *mut crate::leanh::LeanObject,
    mut v___y_2022_: *mut crate::leanh::LeanObject,
    mut v___y_2023_: *mut crate::leanh::LeanObject,
    mut v___y_2024_: *mut crate::leanh::LeanObject,
    mut v___y_2025_: *mut crate::leanh::LeanObject,
    mut v___y_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2028_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___redArg(v_msg_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_);
    return v___x_2028_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_00_u03b1_2029_: *mut crate::leanh::LeanObject,
    mut v_msg_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
    mut v___y_2032_: *mut crate::leanh::LeanObject,
    mut v___y_2033_: *mut crate::leanh::LeanObject,
    mut v___y_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6(v_00_u03b1_2029_, v_msg_2030_, v___y_2031_, v___y_2032_, v___y_2033_, v___y_2034_, v___y_2035_, v___y_2036_);
    crate::leanh::lean_dec(v___y_2036_);
    crate::leanh::lean_dec_ref(v___y_2035_);
    crate::leanh::lean_dec(v___y_2034_);
    crate::leanh::lean_dec_ref(v___y_2033_);
    crate::leanh::lean_dec(v___y_2032_);
    crate::leanh::lean_dec_ref(v___y_2031_);
    return v_res_2038_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(
    mut v_msgData_2039_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
    mut v___y_2043_: *mut crate::leanh::LeanObject,
    mut v___y_2044_: *mut crate::leanh::LeanObject,
    mut v___y_2045_: *mut crate::leanh::LeanObject,
    mut v___y_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2048_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___redArg(v_msgData_2039_, v_macroStack_2040_, v___y_2045_);
    return v___x_2048_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8___boxed(
    mut v_msgData_2049_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
    mut v___y_2052_: *mut crate::leanh::LeanObject,
    mut v___y_2053_: *mut crate::leanh::LeanObject,
    mut v___y_2054_: *mut crate::leanh::LeanObject,
    mut v___y_2055_: *mut crate::leanh::LeanObject,
    mut v___y_2056_: *mut crate::leanh::LeanObject,
    mut v___y_2057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2058_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__8(v_msgData_2049_, v_macroStack_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_);
    crate::leanh::lean_dec(v___y_2056_);
    crate::leanh::lean_dec_ref(v___y_2055_);
    crate::leanh::lean_dec(v___y_2054_);
    crate::leanh::lean_dec_ref(v___y_2053_);
    crate::leanh::lean_dec(v___y_2052_);
    crate::leanh::lean_dec_ref(v___y_2051_);
    return v_res_2058_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = crate::leanh::lean_box(0);
    v___x_2060_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2061_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2061_, 0, v___x_2060_);
    crate::leanh::lean_ctor_set(v___x_2061_, 1, v___x_2059_);
    return v___x_2061_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2063_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___closed__0);
    v___x_2064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2064_, 0, v___x_2063_);
    return v___x_2064_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg___boxed(
    mut v___y_2065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2066_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
    return v_res_2066_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(
    mut v_00_u03b1_2067_: *mut crate::leanh::LeanObject,
    mut v___y_2068_: *mut crate::leanh::LeanObject,
    mut v___y_2069_: *mut crate::leanh::LeanObject,
    mut v___y_2070_: *mut crate::leanh::LeanObject,
    mut v___y_2071_: *mut crate::leanh::LeanObject,
    mut v___y_2072_: *mut crate::leanh::LeanObject,
    mut v___y_2073_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2075_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
    return v___x_2075_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___boxed(
    mut v_00_u03b1_2076_: *mut crate::leanh::LeanObject,
    mut v___y_2077_: *mut crate::leanh::LeanObject,
    mut v___y_2078_: *mut crate::leanh::LeanObject,
    mut v___y_2079_: *mut crate::leanh::LeanObject,
    mut v___y_2080_: *mut crate::leanh::LeanObject,
    mut v___y_2081_: *mut crate::leanh::LeanObject,
    mut v___y_2082_: *mut crate::leanh::LeanObject,
    mut v___y_2083_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2084_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0(v_00_u03b1_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
    crate::leanh::lean_dec(v___y_2082_);
    crate::leanh::lean_dec_ref(v___y_2081_);
    crate::leanh::lean_dec(v___y_2080_);
    crate::leanh::lean_dec_ref(v___y_2079_);
    crate::leanh::lean_dec(v___y_2078_);
    crate::leanh::lean_dec_ref(v___y_2077_);
    return v_res_2084_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0(
    mut v___y_2093_: u8,
    mut v_suppressElabErrors_2094_: u8,
    mut v_x_2095_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_2095_) == 1 {
        let mut v_pre_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_2096_ = crate::leanh::lean_ctor_get(v_x_2095_, 0);
        match crate::leanh::lean_obj_tag(v_pre_2096_) {
            1 => {
                let mut v_pre_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_2097_ = crate::leanh::lean_ctor_get(v_pre_2096_, 0);
                match crate::leanh::lean_obj_tag(v_pre_2097_) {
                    0 => {
                        let mut v_str_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_2101_: u8 = 0;
                        v_str_2098_ = crate::leanh::lean_ctor_get(v_x_2095_, 1);
                        v_str_2099_ = crate::leanh::lean_ctor_get(v_pre_2096_, 1);
                        v___x_2100_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__0;
                        v___x_2101_ = lean_string_dec_eq(v_str_2099_, v___x_2100_);
                        if v___x_2101_ == 0 {
                            let mut v___x_2102_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2103_: u8 = 0;
                            v___x_2102_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__1;
                            v___x_2103_ = lean_string_dec_eq(v_str_2099_, v___x_2102_);
                            if v___x_2103_ == 0 {
                                return v___y_2093_;
                            } else {
                                let mut v___x_2104_: *mut crate::leanh::LeanObject =
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
                            let mut v___x_2106_: *mut crate::leanh::LeanObject =
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
                        let mut v_pre_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_2108_ = crate::leanh::lean_ctor_get(v_pre_2097_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_2108_) == 0 {
                            let mut v_str_2109_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2110_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_2111_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2112_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_2113_: u8 = 0;
                            v_str_2109_ = crate::leanh::lean_ctor_get(v_x_2095_, 1);
                            v_str_2110_ = crate::leanh::lean_ctor_get(v_pre_2096_, 1);
                            v_str_2111_ = crate::leanh::lean_ctor_get(v_pre_2097_, 1);
                            v___x_2112_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__4;
                            v___x_2113_ = lean_string_dec_eq(v_str_2111_, v___x_2112_);
                            if v___x_2113_ == 0 {
                                return v___y_2093_;
                            } else {
                                let mut v___x_2114_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_2115_: u8 = 0;
                                v___x_2114_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___closed__5;
                                v___x_2115_ = lean_string_dec_eq(v_str_2110_, v___x_2114_);
                                if v___x_2115_ == 0 {
                                    return v___y_2093_;
                                } else {
                                    let mut v___x_2116_: *mut crate::leanh::LeanObject =
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
                let mut v_str_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2120_: u8 = 0;
                v_str_2118_ = crate::leanh::lean_ctor_get(v_x_2095_, 1);
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
    mut v___y_2121_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_2122_: *mut crate::leanh::LeanObject,
    mut v_x_2123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3856__boxed_2124_: u8 = 0;
    let mut v_suppressElabErrors_boxed_2125_: u8 = 0;
    let mut v_res_2126_: u8 = 0;
    let mut v_r_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3856__boxed_2124_ = (crate::leanh::lean_unbox(v___y_2121_) as u8);
    v_suppressElabErrors_boxed_2125_ = (crate::leanh::lean_unbox(v_suppressElabErrors_2122_) as u8);
    v_res_2126_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0(v___y_3856__boxed_2124_, v_suppressElabErrors_boxed_2125_, v_x_2123_);
    crate::leanh::lean_dec(v_x_2123_);
    v_r_2127_ = crate::leanh::lean_box((v_res_2126_) as usize);
    return v_r_2127_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(
    mut v_ref_2129_: *mut crate::leanh::LeanObject,
    mut v_msgData_2130_: *mut crate::leanh::LeanObject,
    mut v_severity_2131_: u8,
    mut v_isSilent_2132_: u8,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
    mut v___y_2135_: *mut crate::leanh::LeanObject,
    mut v___y_2136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2139_: u8 = 0;
    let mut v___y_2140_: u8 = 0;
    let mut v___y_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2162_: u8 = 0;
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v___y_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: u8 = 0;
    let mut v___y_2177_: u8 = 0;
    let mut v___y_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2179_: u8 = 0;
    let mut v___y_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut v___y_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2201_: u8 = 0;
    let mut v___y_2202_: u8 = 0;
    let mut v___y_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2205_: u8 = 0;
    let mut v___y_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2212_: u8 = 0;
    let mut v___y_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2214_: u8 = 0;
    let mut v___y_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2217_: u8 = 0;
    let mut v_ref_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: u8 = 0;
    let mut v___y_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2227_: u8 = 0;
    let mut v___y_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2229_: u8 = 0;
    let mut v___y_2230_: u8 = 0;
    let mut v___y_2232_: u8 = 0;
    let mut v_fileName_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2237_: u8 = 0;
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: u8 = 0;
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: u8 = 0;
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
                    crate::leanh::lean_inc_ref(v_msgData_2130_);
                    v___x_2248_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_2130_);
                    v___y_2232_ = v___x_2248_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_2148_ = lean_st_ref_take(v___y_2147_);
                v_currNamespace_2149_ = crate::leanh::lean_ctor_get(v___y_2146_, 6);
                v_openDecls_2150_ = crate::leanh::lean_ctor_get(v___y_2146_, 7);
                v_env_2151_ = crate::leanh::lean_ctor_get(v___x_2148_, 0);
                v_nextMacroScope_2152_ = crate::leanh::lean_ctor_get(v___x_2148_, 1);
                v_ngen_2153_ = crate::leanh::lean_ctor_get(v___x_2148_, 2);
                v_auxDeclNGen_2154_ = crate::leanh::lean_ctor_get(v___x_2148_, 3);
                v_traceState_2155_ = crate::leanh::lean_ctor_get(v___x_2148_, 4);
                v_cache_2156_ = crate::leanh::lean_ctor_get(v___x_2148_, 5);
                v_messages_2157_ = crate::leanh::lean_ctor_get(v___x_2148_, 6);
                v_infoState_2158_ = crate::leanh::lean_ctor_get(v___x_2148_, 7);
                v_snapshotTasks_2159_ = crate::leanh::lean_ctor_get(v___x_2148_, 8);
                v_isSharedCheck_2173_ = (!crate::leanh::lean_is_exclusive(v___x_2148_)) as u8;
                if v_isSharedCheck_2173_ == 0 {
                    v___x_2161_ = v___x_2148_;
                    v_isShared_2162_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2159_);
                    crate::leanh::lean_inc(v_infoState_2158_);
                    crate::leanh::lean_inc(v_messages_2157_);
                    crate::leanh::lean_inc(v_cache_2156_);
                    crate::leanh::lean_inc(v_traceState_2155_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2154_);
                    crate::leanh::lean_inc(v_ngen_2153_);
                    crate::leanh::lean_inc(v_nextMacroScope_2152_);
                    crate::leanh::lean_inc(v_env_2151_);
                    crate::leanh::lean_dec(v___x_2148_);
                    v___x_2161_ = crate::leanh::lean_box(0);
                    v_isShared_2162_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_2150_);
                crate::leanh::lean_inc(v_currNamespace_2149_);
                v___x_2163_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2163_, 0, v_currNamespace_2149_);
                crate::leanh::lean_ctor_set(v___x_2163_, 1, v_openDecls_2150_);
                v___x_2164_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2164_, 0, v___x_2163_);
                crate::leanh::lean_ctor_set(v___x_2164_, 1, v___y_2141_);
                crate::leanh::lean_inc_ref(v___y_2143_);
                crate::leanh::lean_inc_ref(v___y_2145_);
                v___x_2165_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_2165_, 0, v___y_2145_);
                crate::leanh::lean_ctor_set(v___x_2165_, 1, v___y_2142_);
                crate::leanh::lean_ctor_set(v___x_2165_, 2, v___y_2144_);
                crate::leanh::lean_ctor_set(v___x_2165_, 3, v___y_2143_);
                crate::leanh::lean_ctor_set(v___x_2165_, 4, v___x_2164_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_2140_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_2139_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2165_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_2132_,
                );
                v___x_2166_ = l_Lean_MessageLog_add(v___x_2165_, v_messages_2157_);
                if v_isShared_2162_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2161_, 6, v___x_2166_);
                    v___x_2168_ = v___x_2161_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_env_2151_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_nextMacroScope_2152_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_ngen_2153_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_auxDeclNGen_2154_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 4, v_traceState_2155_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_cache_2156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 6, v___x_2166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_infoState_2158_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_snapshotTasks_2159_);
                    v___x_2168_ = v_reuseFailAlloc_2172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2169_ = lean_st_ref_set(v___y_2147_, v___x_2168_);
                v___x_2170_ = crate::leanh::lean_box(0);
                v___x_2171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2171_, 0, v___x_2170_);
                return v___x_2171_;
            }
            4 => {
                v___x_2183_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_2130_,
                    );
                v___x_2184_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType_spec__0_spec__0_spec__1_spec__2_spec__4_spec__6_spec__7(v___x_2183_, v___y_2133_, v___y_2134_, v___y_2135_, v___y_2136_);
                v_a_2185_ = crate::leanh::lean_ctor_get(v___x_2184_, 0);
                v_isSharedCheck_2198_ = (!crate::leanh::lean_is_exclusive(v___x_2184_)) as u8;
                if v_isSharedCheck_2198_ == 0 {
                    v___x_2187_ = v___x_2184_;
                    v_isShared_2188_ = v_isSharedCheck_2198_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2185_);
                    crate::leanh::lean_dec(v___x_2184_);
                    v___x_2187_ = crate::leanh::lean_box(0);
                    v_isShared_2188_ = v_isSharedCheck_2198_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_2180_, 2);
                v___x_2189_ = l_Lean_FileMap_toPosition(v___y_2180_, v___y_2178_);
                crate::leanh::lean_dec(v___y_2178_);
                v___x_2190_ = l_Lean_FileMap_toPosition(v___y_2180_, v___y_2182_);
                crate::leanh::lean_dec(v___y_2182_);
                v___x_2191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2191_, 0, v___x_2190_);
                v___x_2192_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___closed__0;
                if v___y_2179_ == 0 {
                    crate::leanh::lean_del_object(v___x_2187_);
                    crate::leanh::lean_dec_ref(v___y_2175_);
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
                    crate::leanh::lean_inc(v_a_2185_);
                    v___x_2193_ = l_Lean_MessageData_hasTag(v___y_2175_, v_a_2185_);
                    if v___x_2193_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2191_, 1);
                        crate::leanh::lean_dec_ref(v___x_2189_);
                        crate::leanh::lean_dec(v_a_2185_);
                        v___x_2194_ = crate::leanh::lean_box(0);
                        if v_isShared_2188_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2187_, 0, v___x_2194_);
                            v___x_2196_ = v___x_2187_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_2197_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2194_);
                            v___x_2196_ = v_reuseFailAlloc_2197_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2187_);
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
                crate::leanh::lean_dec(v___y_2203_);
                if crate::leanh::lean_obj_tag(v___x_2208_) == 0 {
                    crate::leanh::lean_inc(v___y_2207_);
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
                    v_val_2209_ = crate::leanh::lean_ctor_get(v___x_2208_, 0);
                    crate::leanh::lean_inc(v_val_2209_);
                    crate::leanh::lean_dec_ref_known(v___x_2208_, 1);
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
                if crate::leanh::lean_obj_tag(v___x_2219_) == 0 {
                    v___x_2220_ = crate::leanh::lean_unsigned_to_nat(0);
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
                    v_val_2221_ = crate::leanh::lean_ctor_get(v___x_2219_, 0);
                    crate::leanh::lean_inc(v_val_2221_);
                    crate::leanh::lean_dec_ref_known(v___x_2219_, 1);
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
                    v_fileName_2233_ = crate::leanh::lean_ctor_get(v___y_2135_, 0);
                    v_fileMap_2234_ = crate::leanh::lean_ctor_get(v___y_2135_, 1);
                    v_options_2235_ = crate::leanh::lean_ctor_get(v___y_2135_, 2);
                    v_ref_2236_ = crate::leanh::lean_ctor_get(v___y_2135_, 5);
                    v_suppressElabErrors_2237_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2135_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_2238_ = crate::leanh::lean_box((v___y_2232_) as usize);
                    v___x_2239_ = crate::leanh::lean_box((v_suppressElabErrors_2237_) as usize);
                    v___f_2240_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_2240_, 0, v___x_2238_);
                    crate::leanh::lean_closure_set(v___f_2240_, 1, v___x_2239_);
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
                    crate::leanh::lean_dec_ref(v_msgData_2130_);
                    v___x_2245_ = crate::leanh::lean_box(0);
                    v___x_2246_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2246_, 0, v___x_2245_);
                    return v___x_2246_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_ref_2249_: *mut crate::leanh::LeanObject,
    mut v_msgData_2250_: *mut crate::leanh::LeanObject,
    mut v_severity_2251_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2252_: *mut crate::leanh::LeanObject,
    mut v___y_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2258_: u8 = 0;
    let mut v_isSilent_boxed_2259_: u8 = 0;
    let mut v_res_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2258_ = (crate::leanh::lean_unbox(v_severity_2251_) as u8);
    v_isSilent_boxed_2259_ = (crate::leanh::lean_unbox(v_isSilent_2252_) as u8);
    v_res_2260_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(v_ref_2249_, v_msgData_2250_, v_severity_boxed_2258_, v_isSilent_boxed_2259_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
    crate::leanh::lean_dec(v___y_2256_);
    crate::leanh::lean_dec_ref(v___y_2255_);
    crate::leanh::lean_dec(v___y_2254_);
    crate::leanh::lean_dec_ref(v___y_2253_);
    crate::leanh::lean_dec(v_ref_2249_);
    return v_res_2260_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1(
    mut v_msgData_2261_: *mut crate::leanh::LeanObject,
    mut v_severity_2262_: u8,
    mut v_isSilent_2263_: u8,
    mut v___y_2264_: *mut crate::leanh::LeanObject,
    mut v___y_2265_: *mut crate::leanh::LeanObject,
    mut v___y_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2271_ = crate::leanh::lean_ctor_get(v___y_2268_, 5);
    v___x_2272_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(v_ref_2271_, v_msgData_2261_, v_severity_2262_, v_isSilent_2263_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_);
    return v___x_2272_;
}
pub unsafe fn l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1___boxed(
    mut v_msgData_2273_: *mut crate::leanh::LeanObject,
    mut v_severity_2274_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2275_: *mut crate::leanh::LeanObject,
    mut v___y_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
    mut v___y_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2283_: u8 = 0;
    let mut v_isSilent_boxed_2284_: u8 = 0;
    let mut v_res_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2283_ = (crate::leanh::lean_unbox(v_severity_2274_) as u8);
    v_isSilent_boxed_2284_ = (crate::leanh::lean_unbox(v_isSilent_2275_) as u8);
    v_res_2285_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1(v_msgData_2273_, v_severity_boxed_2283_, v_isSilent_boxed_2284_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
    crate::leanh::lean_dec(v___y_2281_);
    crate::leanh::lean_dec_ref(v___y_2280_);
    crate::leanh::lean_dec(v___y_2279_);
    crate::leanh::lean_dec_ref(v___y_2278_);
    crate::leanh::lean_dec(v___y_2277_);
    crate::leanh::lean_dec_ref(v___y_2276_);
    return v_res_2285_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(
    mut v_msgData_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
    mut v___y_2292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2294_: u8 = 0;
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2294_ = 0;
    v___x_2295_ = 0;
    v___x_2296_ = l_Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1(v_msgData_2286_, v___x_2294_, v___x_2295_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_, v___y_2292_);
    return v___x_2296_;
}
pub unsafe fn l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1___boxed(
    mut v_msgData_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
    mut v___y_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2305_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(
        v_msgData_2297_,
        v___y_2298_,
        v___y_2299_,
        v___y_2300_,
        v___y_2301_,
        v___y_2302_,
        v___y_2303_,
    );
    crate::leanh::lean_dec(v___y_2303_);
    crate::leanh::lean_dec_ref(v___y_2302_);
    crate::leanh::lean_dec(v___y_2301_);
    crate::leanh::lean_dec_ref(v___y_2300_);
    crate::leanh::lean_dec(v___y_2299_);
    crate::leanh::lean_dec_ref(v___y_2298_);
    return v_res_2305_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0(
    mut v___x_2306_: u8,
    mut v_stx_2307_: *mut crate::leanh::LeanObject,
    mut v___y_2308_: *mut crate::leanh::LeanObject,
    mut v___y_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2329_: u8 = 0;
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2333_: u8 = 0;
    let mut v_a_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2337_: u8 = 0;
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2345_: u8 = 0;
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2349_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2306_ == 0 {
                    v___x_2315_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
                    return v___x_2315_;
                } else {
                    v___x_2316_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_t_2317_ = l_Lean_Syntax_getArg(v_stx_2307_, v___x_2316_);
                    v___x_2318_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(v_t_2317_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                    if crate::leanh::lean_obj_tag(v___x_2318_) == 0 {
                        v_a_2319_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                        crate::leanh::lean_inc(v_a_2319_);
                        crate::leanh::lean_dec_ref_known(v___x_2318_, 1);
                        v___x_2320_ = 0;
                        v___x_2321_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(v_a_2319_, v___x_2320_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                        if crate::leanh::lean_obj_tag(v___x_2321_) == 0 {
                            v_a_2322_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                            crate::leanh::lean_inc(v_a_2322_);
                            crate::leanh::lean_dec_ref_known(v___x_2321_, 1);
                            v___x_2323_ = l_Lean_Meta_DiscrTree_keysAsPattern(
                                v_a_2322_,
                                v___y_2312_,
                                v___y_2313_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2323_) == 0 {
                                v_a_2324_ = crate::leanh::lean_ctor_get(v___x_2323_, 0);
                                crate::leanh::lean_inc(v_a_2324_);
                                crate::leanh::lean_dec_ref_known(v___x_2323_, 1);
                                v___x_2325_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(v_a_2324_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                                return v___x_2325_;
                            } else {
                                v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2323_, 0);
                                v_isSharedCheck_2333_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2323_)) as u8;
                                if v_isSharedCheck_2333_ == 0 {
                                    v___x_2328_ = v___x_2323_;
                                    v_isShared_2329_ = v_isSharedCheck_2333_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2326_);
                                    crate::leanh::lean_dec(v___x_2323_);
                                    v___x_2328_ = crate::leanh::lean_box(0);
                                    v_isShared_2329_ = v_isSharedCheck_2333_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_2334_ = crate::leanh::lean_ctor_get(v___x_2321_, 0);
                            v_isSharedCheck_2341_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2321_)) as u8;
                            if v_isSharedCheck_2341_ == 0 {
                                v___x_2336_ = v___x_2321_;
                                v_isShared_2337_ = v_isSharedCheck_2341_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2334_);
                                crate::leanh::lean_dec(v___x_2321_);
                                v___x_2336_ = crate::leanh::lean_box(0);
                                v_isShared_2337_ = v_isSharedCheck_2341_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_2342_ = crate::leanh::lean_ctor_get(v___x_2318_, 0);
                        v_isSharedCheck_2349_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2318_)) as u8;
                        if v_isSharedCheck_2349_ == 0 {
                            v___x_2344_ = v___x_2318_;
                            v_isShared_2345_ = v_isSharedCheck_2349_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2342_);
                            crate::leanh::lean_dec(v___x_2318_);
                            v___x_2344_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
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
                    v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v_a_2334_);
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
                    v_reuseFailAlloc_2348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_a_2342_);
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
    mut v___x_2350_: *mut crate::leanh::LeanObject,
    mut v_stx_2351_: *mut crate::leanh::LeanObject,
    mut v___y_2352_: *mut crate::leanh::LeanObject,
    mut v___y_2353_: *mut crate::leanh::LeanObject,
    mut v___y_2354_: *mut crate::leanh::LeanObject,
    mut v___y_2355_: *mut crate::leanh::LeanObject,
    mut v___y_2356_: *mut crate::leanh::LeanObject,
    mut v___y_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4185__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4185__boxed_2359_ = (crate::leanh::lean_unbox(v___x_2350_) as u8);
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
    crate::leanh::lean_dec(v___y_2357_);
    crate::leanh::lean_dec_ref(v___y_2356_);
    crate::leanh::lean_dec(v___y_2355_);
    crate::leanh::lean_dec_ref(v___y_2354_);
    crate::leanh::lean_dec(v___y_2353_);
    crate::leanh::lean_dec_ref(v___y_2352_);
    crate::leanh::lean_dec(v_stx_2351_);
    return v_res_2360_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(
    mut v_stx_2368_: *mut crate::leanh::LeanObject,
    mut v_a_2369_: *mut crate::leanh::LeanObject,
    mut v_a_2370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3;
    crate::leanh::lean_inc(v_stx_2368_);
    v___x_2373_ = l_Lean_Syntax_isOfKind(v_stx_2368_, v___x_2372_);
    v___x_2374_ = crate::leanh::lean_box((v___x_2373_) as usize);
    v___y_2375_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___lam__0___boxed
            as *mut core::ffi::c_void,
        9,
        2,
    );
    crate::leanh::lean_closure_set(v___y_2375_, 0, v___x_2374_);
    crate::leanh::lean_closure_set(v___y_2375_, 1, v_stx_2368_);
    v___x_2376_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_2375_, v_a_2369_, v_a_2370_);
    return v___x_2376_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___boxed(
    mut v_stx_2377_: *mut crate::leanh::LeanObject,
    mut v_a_2378_: *mut crate::leanh::LeanObject,
    mut v_a_2379_: *mut crate::leanh::LeanObject,
    mut v_a_2380_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2381_ =
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd(v_stx_2377_, v_a_2378_, v_a_2379_);
    crate::leanh::lean_dec(v_a_2379_);
    crate::leanh::lean_dec_ref(v_a_2378_);
    return v_res_2381_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2(
    mut v_ref_2382_: *mut crate::leanh::LeanObject,
    mut v_msgData_2383_: *mut crate::leanh::LeanObject,
    mut v_severity_2384_: u8,
    mut v_isSilent_2385_: u8,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2393_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___redArg(v_ref_2382_, v_msgData_2383_, v_severity_2384_, v_isSilent_2385_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
    return v___x_2393_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2___boxed(
    mut v_ref_2394_: *mut crate::leanh::LeanObject,
    mut v_msgData_2395_: *mut crate::leanh::LeanObject,
    mut v_severity_2396_: *mut crate::leanh::LeanObject,
    mut v_isSilent_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_2405_: u8 = 0;
    let mut v_isSilent_boxed_2406_: u8 = 0;
    let mut v_res_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_2405_ = (crate::leanh::lean_unbox(v_severity_2396_) as u8);
    v_isSilent_boxed_2406_ = (crate::leanh::lean_unbox(v_isSilent_2397_) as u8);
    v_res_2407_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1_spec__1_spec__2(v_ref_2394_, v_msgData_2395_, v_severity_boxed_2405_, v_isSilent_boxed_2406_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
    crate::leanh::lean_dec(v___y_2403_);
    crate::leanh::lean_dec_ref(v___y_2402_);
    crate::leanh::lean_dec(v___y_2401_);
    crate::leanh::lean_dec_ref(v___y_2400_);
    crate::leanh::lean_dec(v___y_2399_);
    crate::leanh::lean_dec_ref(v___y_2398_);
    crate::leanh::lean_dec(v_ref_2394_);
    return v_res_2407_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2417_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2418_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___closed__3;
    v___x_2419_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1___closed__2;
    v___x_2420_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1();
    return v_res_2423_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0(
    mut v___x_2424_: u8,
    mut v_stx_2425_: *mut crate::leanh::LeanObject,
    mut v___x_2426_: u8,
    mut v___y_2427_: *mut crate::leanh::LeanObject,
    mut v___y_2428_: *mut crate::leanh::LeanObject,
    mut v___y_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut v_a_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2459_: u8 = 0;
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v___x_2424_ == 0 {
                    v___x_2434_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__0___redArg();
                    return v___x_2434_;
                } else {
                    v___x_2435_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_t_2436_ = l_Lean_Syntax_getArg(v_stx_2425_, v___x_2435_);
                    v___x_2437_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_getType(v_t_2436_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
                    if crate::leanh::lean_obj_tag(v___x_2437_) == 0 {
                        v_a_2438_ = crate::leanh::lean_ctor_get(v___x_2437_, 0);
                        crate::leanh::lean_inc(v_a_2438_);
                        crate::leanh::lean_dec_ref_known(v___x_2437_, 1);
                        v___x_2439_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_mkKey(v_a_2438_, v___x_2426_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
                        if crate::leanh::lean_obj_tag(v___x_2439_) == 0 {
                            v_a_2440_ = crate::leanh::lean_ctor_get(v___x_2439_, 0);
                            crate::leanh::lean_inc(v_a_2440_);
                            crate::leanh::lean_dec_ref_known(v___x_2439_, 1);
                            v___x_2441_ = l_Lean_Meta_DiscrTree_keysAsPattern(
                                v_a_2440_,
                                v___y_2431_,
                                v___y_2432_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2441_) == 0 {
                                v_a_2442_ = crate::leanh::lean_ctor_get(v___x_2441_, 0);
                                crate::leanh::lean_inc(v_a_2442_);
                                crate::leanh::lean_dec_ref_known(v___x_2441_, 1);
                                v___x_2443_ = l_Lean_logInfo___at___00Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd_spec__1(v_a_2442_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
                                return v___x_2443_;
                            } else {
                                v_a_2444_ = crate::leanh::lean_ctor_get(v___x_2441_, 0);
                                v_isSharedCheck_2451_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2441_)) as u8;
                                if v_isSharedCheck_2451_ == 0 {
                                    v___x_2446_ = v___x_2441_;
                                    v_isShared_2447_ = v_isSharedCheck_2451_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2444_);
                                    crate::leanh::lean_dec(v___x_2441_);
                                    v___x_2446_ = crate::leanh::lean_box(0);
                                    v_isShared_2447_ = v_isSharedCheck_2451_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            v_a_2452_ = crate::leanh::lean_ctor_get(v___x_2439_, 0);
                            v_isSharedCheck_2459_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2439_)) as u8;
                            if v_isSharedCheck_2459_ == 0 {
                                v___x_2454_ = v___x_2439_;
                                v_isShared_2455_ = v_isSharedCheck_2459_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2452_);
                                crate::leanh::lean_dec(v___x_2439_);
                                v___x_2454_ = crate::leanh::lean_box(0);
                                v_isShared_2455_ = v_isSharedCheck_2459_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        v_a_2460_ = crate::leanh::lean_ctor_get(v___x_2437_, 0);
                        v_isSharedCheck_2467_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2437_)) as u8;
                        if v_isSharedCheck_2467_ == 0 {
                            v___x_2462_ = v___x_2437_;
                            v_isShared_2463_ = v_isSharedCheck_2467_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2460_);
                            crate::leanh::lean_dec(v___x_2437_);
                            v___x_2462_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
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
                    v_reuseFailAlloc_2458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
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
                    v_reuseFailAlloc_2466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
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
    mut v___x_2468_: *mut crate::leanh::LeanObject,
    mut v_stx_2469_: *mut crate::leanh::LeanObject,
    mut v___x_2470_: *mut crate::leanh::LeanObject,
    mut v___y_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_589__boxed_2478_: u8 = 0;
    let mut v___x_590__boxed_2479_: u8 = 0;
    let mut v_res_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_589__boxed_2478_ = (crate::leanh::lean_unbox(v___x_2468_) as u8);
    v___x_590__boxed_2479_ = (crate::leanh::lean_unbox(v___x_2470_) as u8);
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
    crate::leanh::lean_dec(v___y_2476_);
    crate::leanh::lean_dec_ref(v___y_2475_);
    crate::leanh::lean_dec(v___y_2474_);
    crate::leanh::lean_dec_ref(v___y_2473_);
    crate::leanh::lean_dec(v___y_2472_);
    crate::leanh::lean_dec_ref(v___y_2471_);
    crate::leanh::lean_dec(v_stx_2469_);
    return v_res_2480_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(
    mut v_stx_2486_: *mut crate::leanh::LeanObject,
    mut v_a_2487_: *mut crate::leanh::LeanObject,
    mut v_a_2488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    let mut v___x_2492_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2490_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1;
    crate::leanh::lean_inc(v_stx_2486_);
    v___x_2491_ = l_Lean_Syntax_isOfKind(v_stx_2486_, v___x_2490_);
    v___x_2492_ = 1;
    v___x_2493_ = crate::leanh::lean_box((v___x_2491_) as usize);
    v___x_2494_ = crate::leanh::lean_box((v___x_2492_) as usize);
    v___y_2495_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___lam__0___boxed
            as *mut core::ffi::c_void,
        10,
        3,
    );
    crate::leanh::lean_closure_set(v___y_2495_, 0, v___x_2493_);
    crate::leanh::lean_closure_set(v___y_2495_, 1, v_stx_2486_);
    crate::leanh::lean_closure_set(v___y_2495_, 2, v___x_2494_);
    v___x_2496_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___y_2495_, v_a_2487_, v_a_2488_);
    return v___x_2496_;
}
pub unsafe fn l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___boxed(
    mut v_stx_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
    mut v_a_2500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2501_ =
        l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd(v_stx_2497_, v_a_2498_, v_a_2499_);
    crate::leanh::lean_dec(v_a_2499_);
    crate::leanh::lean_dec_ref(v_a_2498_);
    return v_res_2501_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2510_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2511_ = l_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___closed__1;
    v___x_2512_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1___closed__1;
    v___x_2513_ = crate::leanh::lean_alloc_closure(
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
    mut v_a_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2516_ = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1();
    return v_res_2516_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_DiscrTreeKey(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeKeyCmd__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_DiscrTreeKey_0__Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd___regBuiltin_Lean_Elab_Tactic_DiscrTreeKey_evalDiscrTreeSimpKeyCmd__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_DiscrTreeKey(
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
pub unsafe fn initialize_Lean_Elab_Tactic_DiscrTreeKey(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_DiscrTreeKey(builtin);
}
