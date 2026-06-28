// Lean compiler output
// Module: Lake.DSL.Package
// Imports: Lake.DSL.Syntax Lake.Config.Package Lake.DSL.Extensions
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_TSepArray_getElems___redArg,
    l_Lean_Syntax_isNone, l_Lean_Syntax_mkCApp, l_Lean_Syntax_mkNumLit, l_Lean_TSyntax_getId,
    l_Lean_mkIdentFrom, l_Lean_mkOptionalNode,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_throwErrorAt___redArg,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getHeadInfo,
    l_Lean_Syntax_getOptional_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
    l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4,
    l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_Syntax_node7, l_Lean_addMacroScope,
    l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Lake::Config::Package::{
    initialize_Lake_Config_Package, runtime_initialize_Lake_Config_Package,
};
use crate::r#gen::Lake::Config::PackageConfig::l_Lake_PackageConfig_instConfigInfo;
use crate::r#gen::Lake::DSL::DeclUtil::{
    l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields, l_Lake_DSL_expandAttrs,
    l_Lake_DSL_expandOptSimpleBinder, l_Lake_DSL_mkConfigDeclIdent, l_Lake_DSL_packageDeclName,
};
use crate::r#gen::Lake::DSL::Extensions::{
    initialize_Lake_DSL_Extensions, l_Lake_nameExt, runtime_initialize_Lake_DSL_Extensions,
};
use crate::r#gen::Lake::DSL::Syntax::{
    initialize_Lake_DSL_Syntax, runtime_initialize_Lake_DSL_Syntax,
};
use crate::r#gen::Lake::Util::Name::l_Lake_Name_quoteFrom;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_elabCommand,
    l_Lean_Elab_Command_elabCommand___boxed, l_Lean_Elab_Command_getCurrMacroScope___redArg,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_withMacroExpansion___redArg,
};
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_getBetterRef, l_Lean_Elab_macroAttribute, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_header,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofSyntax, l_Lean_indentD,
    l_Lean_stringToMessageData,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [119, 104, 101, 114, 101, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 101, 114, 101, 83, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value) as *mut crate::leanh::LeanObject,7794500365561932708 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 83, 76, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value) as *mut crate::leanh::LeanObject,2937396280676515247 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value: crate::leanh::LeanStringObject<32> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 101, 99, 108, 86, 97, 108, 87, 104, 101, 114, 101, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value) as *mut crate::leanh::LeanObject,5906021167542994327 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 116, 114, 117, 99, 116, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value) as *mut crate::leanh::LeanObject,1004026287653508741 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 116, 114, 117, 99, 116, 86, 97, 108, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value) as *mut crate::leanh::LeanObject,10845500395294116975 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value) as *mut crate::leanh::LeanObject,5018042693327868416 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [119, 104, 101, 114, 101, 68, 101, 99, 108, 115, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value) as *mut crate::leanh::LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value) as *mut crate::leanh::LeanObject,4503069825835506739 as *mut crate::leanh::LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value:
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
    m_data: [100, 101, 112, 114, 101, 99, 97, 116, 101, 100, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value:
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
    m_data: [115, 116, 114, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        9232979286016572671 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        34, 85, 115, 101, 32, 96, 95, 95, 110, 97, 109, 101, 95, 95, 96, 32, 105, 110, 115, 116,
        101, 97, 100, 46, 34, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [40, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value:
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
    m_data: [115, 105, 110, 99, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [34, 50, 48, 50, 53, 45, 48, 57, 45, 49, 56, 34, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value:
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
    m_data: [110, 97, 109, 101, 67, 111, 110, 115, 116, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        12277407653222002017 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [95, 95, 110, 97, 109, 101, 95, 95, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        112, 97, 99, 107, 97, 103, 101, 67, 111, 109, 109, 97, 110, 100, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value
        ) as *mut crate::leanh::LeanObject,
        3605886163266385533 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value:
    crate::leanh::LeanStringObject<31> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 112, 97, 99, 107, 97, 103, 101, 32,
        100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value:
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
    m_data: [97, 116, 116, 114, 105, 98, 117, 116, 101, 115, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [64, 91, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [93, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value:
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
    m_data: [97, 98, 98, 114, 101, 118, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [80, 97, 99, 107, 97, 103, 101, 68, 101, 99, 108, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value
        ) as *mut crate::leanh::LeanObject,
        9855517672881652961 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value
        ) as *mut crate::leanh::LeanObject,
        14292882441629431293 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        100, 101, 99, 108, 86, 97, 108, 83, 105, 109, 112, 108, 101, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [84, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value:
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
    m_data: [115, 117, 102, 102, 105, 120, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value:
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
    m_data: [110, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value:
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
    m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [123, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value:
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
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 76, 86, 97, 108, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 97, 115, 101, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value
        ) as *mut crate::leanh::LeanObject,
        13060808746942009198 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 68, 101, 102, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 61, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [44, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [111, 114, 105, 103, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value
        ) as *mut crate::leanh::LeanObject,
        5783777625530456636 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value:
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
    m_data: [107, 101, 121, 78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value
        ) as *mut crate::leanh::LeanObject,
        1448088012876701721 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value:
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
    m_data: [99, 111, 110, 102, 105, 103, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value
        ) as *mut crate::leanh::LeanObject,
        14398486047628956367 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [111, 112, 116, 69, 108, 108, 105, 112, 115, 105, 115, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [125, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 9,
    m_data: [194, 171, 112, 97, 99, 107, 97, 103, 101, 194, 187, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value:
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
    m_data: [112, 97, 99, 107, 97, 103, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value
        ) as *mut crate::leanh::LeanObject,
        6671755061125946191 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value:
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
    m_data: [65, 116, 116, 114, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value:
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
    m_data: [115, 105, 109, 112, 108, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value:
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
    m_data: [78, 97, 109, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value:
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
    m_data: [110, 117, 109, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_1:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value
        ) as *mut crate::leanh::LeanObject,
        13306843946249674491 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value
        ) as *mut crate::leanh::LeanObject,
        7229350633979142691 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [
        80, 97, 99, 107, 97, 103, 101, 67, 111, 110, 102, 105, 103, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value
        ) as *mut crate::leanh::LeanObject,
        15699985925601833486 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value:
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
    m_data: [112, 107, 103, 67, 111, 110, 102, 105, 103, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value
        ) as *mut crate::leanh::LeanObject,
        5998648494902257236 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,12997130533650095963 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,11286550318989764116 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [80, 97, 99, 107, 97, 103, 101, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value) as *mut crate::leanh::LeanObject,15681734397375188879 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16086747790069339938 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,11922365661391839154 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,17745535245540040497 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 80, 97, 99, 107, 97, 103, 101, 67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value) as *mut crate::leanh::LeanObject,17339603636372616795 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 68, 101, 99, 108, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        7248721378401769890 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value:
    crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 112, 111, 115, 116, 95, 117, 112, 100,
        97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value:
    crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        112, 111, 115, 116, 85, 112, 100, 97, 116, 101, 72, 111, 111, 107, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        14712175129652721653 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value:
    crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        80, 111, 115, 116, 85, 112, 100, 97, 116, 101, 72, 111, 111, 107, 68, 101, 99, 108, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        5750662100507400969 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value
        ) as *mut crate::leanh::LeanObject,
        1387310164323292101 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value
        ) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value:
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
    m_data: [112, 107, 103, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value
        ) as *mut crate::leanh::LeanObject,
        16251518922638631496 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [102, 110, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        1077391322905290683 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value:
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
    m_data: [102, 117, 110, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [98, 97, 115, 105, 99, 70, 117, 110, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [61, 62, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 13,
    m_data: [
        194, 171, 112, 111, 115, 116, 95, 117, 112, 100, 97, 116, 101, 194, 187, 0,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [112, 111, 115, 116, 95, 117, 112, 100, 97, 116, 101, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value:
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
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value
        ) as *mut crate::leanh::LeanObject,
        985716791886485019 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value:
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
    m_data: [100, 101, 99, 108, 86, 97, 108, 68, 111, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut crate::leanh::LeanObject,13012506173997729135 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut crate::leanh::LeanObject,5901868804703194544 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value
        ) as *mut crate::leanh::LeanObject,
        11022427548561232637 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value) as *mut crate::leanh::LeanObject,17342580262104060118 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value
        ) as *mut crate::leanh::LeanObject,
        13585030837571646948 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value
        ) as *mut crate::leanh::LeanObject,
        7625897890118033792 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value
        ) as *mut crate::leanh::LeanObject,
        8715860392475343861 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [100, 111, 0],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value
) as *mut crate::leanh::LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value:
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
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value
        ) as *mut crate::leanh::LeanObject,
        5817315006727311029 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 85, 112, 100, 97, 116, 101, 68, 101, 99, 108, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value) as *mut crate::leanh::LeanObject,6329611640435385135 as *mut crate::leanh::LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(
    mut v___y_1802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1804_ = lean_st_ref_get(v___y_1802_);
    v_env_1805_ = crate::leanh::lean_ctor_get(v___x_1804_, 0);
    crate::leanh::lean_inc_ref(v_env_1805_);
    crate::leanh::lean_dec(v___x_1804_);
    v___x_1806_ = l_Lean_Environment_header(v_env_1805_);
    crate::leanh::lean_dec_ref(v_env_1805_);
    v_mainModule_1807_ = crate::leanh::lean_ctor_get(v___x_1806_, 0);
    crate::leanh::lean_inc(v_mainModule_1807_);
    crate::leanh::lean_dec_ref(v___x_1806_);
    v___x_1808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1808_, 0, v_mainModule_1807_);
    return v___x_1808_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg___boxed(
    mut v___y_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1811_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1809_);
    crate::leanh::lean_dec(v___y_1809_);
    return v_res_1811_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(
    mut v___y_1812_: *mut crate::leanh::LeanObject,
    mut v___y_1813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1815_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1813_);
    return v___x_1815_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___boxed(
    mut v___y_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(v___y_1816_, v___y_1817_);
    crate::leanh::lean_dec(v___y_1817_);
    crate::leanh::lean_dec_ref(v___y_1816_);
    return v_res_1819_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
    mut v___y_1820_: *mut crate::leanh::LeanObject,
    mut v___y_1821_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut v_a_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1837_: u8 = 0;
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1823_ = l_Lean_Elab_Command_getRef___redArg(v___y_1820_);
                if crate::leanh::lean_obj_tag(v___x_1823_) == 0 {
                    v_a_1824_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1833_ = (!crate::leanh::lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1833_ == 0 {
                        v___x_1826_ = v___x_1823_;
                        v_isShared_1827_ = v_isSharedCheck_1833_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1824_);
                        crate::leanh::lean_dec(v___x_1823_);
                        v___x_1826_ = crate::leanh::lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1833_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1834_ = crate::leanh::lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1841_ = (!crate::leanh::lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1841_ == 0 {
                        v___x_1836_ = v___x_1823_;
                        v_isShared_1837_ = v_isSharedCheck_1841_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1834_);
                        crate::leanh::lean_dec(v___x_1823_);
                        v___x_1836_ = crate::leanh::lean_box(0);
                        v_isShared_1837_ = v_isSharedCheck_1841_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1828_ = 0;
                v___x_1829_ = l_Lean_SourceInfo_fromRef(v_a_1824_, v___x_1828_);
                crate::leanh::lean_dec(v_a_1824_);
                if v_isShared_1827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
                    v___x_1831_ = v_reuseFailAlloc_1832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1831_;
            }
            3 => {
                if v_isShared_1837_ == 0 {
                    v___x_1839_ = v___x_1836_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
                    v___x_1839_ = v_reuseFailAlloc_1840_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1839_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0___boxed(
    mut v___y_1842_: *mut crate::leanh::LeanObject,
    mut v___y_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
        v___y_1842_,
        v___y_1843_,
    );
    crate::leanh::lean_dec(v___y_1843_);
    crate::leanh::lean_dec_ref(v___y_1842_);
    return v_res_1845_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1846_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_1848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1848_, 0, v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_1850_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1851_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1851_, 0, v___x_1850_);
    crate::leanh::lean_ctor_set(v___x_1851_, 1, v___x_1850_);
    crate::leanh::lean_ctor_set(v___x_1851_, 2, v___x_1850_);
    crate::leanh::lean_ctor_set(v___x_1851_, 3, v___x_1850_);
    crate::leanh::lean_ctor_set(v___x_1851_, 4, v___x_1849_);
    crate::leanh::lean_ctor_set(v___x_1851_, 5, v___x_1849_);
    crate::leanh::lean_ctor_set(v___x_1851_, 6, v___x_1849_);
    crate::leanh::lean_ctor_set(v___x_1851_, 7, v___x_1849_);
    crate::leanh::lean_ctor_set(v___x_1851_, 8, v___x_1849_);
    crate::leanh::lean_ctor_set(v___x_1851_, 9, v___x_1849_);
    return v___x_1851_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1852_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1853_ = lean_mk_empty_array_with_capacity(v___x_1852_);
    v___x_1854_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1854_, 0, v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1855_ = 5usize;
    v___x_1856_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1857_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1858_ = lean_mk_empty_array_with_capacity(v___x_1857_);
    v___x_1859_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_1860_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    crate::leanh::lean_ctor_set(v___x_1860_, 1, v___x_1858_);
    crate::leanh::lean_ctor_set(v___x_1860_, 2, v___x_1856_);
    crate::leanh::lean_ctor_set(v___x_1860_, 3, v___x_1856_);
    crate::leanh::lean_ctor_set_usize(v___x_1860_, 4, v___x_1855_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1861_ = crate::leanh::lean_box(1);
    v___x_1862_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4);
    v___x_1863_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_1864_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1864_, 0, v___x_1863_);
    crate::leanh::lean_ctor_set(v___x_1864_, 1, v___x_1862_);
    crate::leanh::lean_ctor_set(v___x_1864_, 2, v___x_1861_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1868_ = lean_st_ref_get(v___y_1866_);
    v_env_1869_ = crate::leanh::lean_ctor_get(v___x_1868_, 0);
    crate::leanh::lean_inc_ref(v_env_1869_);
    crate::leanh::lean_dec(v___x_1868_);
    v___x_1870_ = lean_st_ref_get(v___y_1866_);
    v_scopes_1871_ = crate::leanh::lean_ctor_get(v___x_1870_, 2);
    crate::leanh::lean_inc(v_scopes_1871_);
    crate::leanh::lean_dec(v___x_1870_);
    v___x_1872_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1873_ = l_List_head_x21___redArg(v___x_1872_, v_scopes_1871_);
    crate::leanh::lean_dec(v_scopes_1871_);
    v_opts_1874_ = crate::leanh::lean_ctor_get(v___x_1873_, 1);
    crate::leanh::lean_inc_ref(v_opts_1874_);
    crate::leanh::lean_dec(v___x_1873_);
    v___x_1875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2);
    v___x_1876_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5);
    v___x_1877_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1877_, 0, v_env_1869_);
    crate::leanh::lean_ctor_set(v___x_1877_, 1, v___x_1875_);
    crate::leanh::lean_ctor_set(v___x_1877_, 2, v___x_1876_);
    crate::leanh::lean_ctor_set(v___x_1877_, 3, v_opts_1874_);
    v___x_1878_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1878_, 0, v___x_1877_);
    crate::leanh::lean_ctor_set(v___x_1878_, 1, v_msgData_1865_);
    v___x_1879_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1879_, 0, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_1880_: *mut crate::leanh::LeanObject,
    mut v___y_1881_: *mut crate::leanh::LeanObject,
    mut v___y_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1880_, v___y_1881_);
    crate::leanh::lean_dec(v___y_1881_);
    return v_res_1883_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1884_ = crate::leanh::lean_box(1);
    v___x_1885_ = l_Lean_MessageData_ofFormat(v___x_1884_);
    return v___x_1885_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2;
    v___x_1890_ = l_Lean_MessageData_ofFormat(v___x_1889_);
    return v___x_1890_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(
    mut v_x_1891_: *mut crate::leanh::LeanObject,
    mut v_x_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v_before_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1914_: u8 = 0;
    let mut v_unused_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1892_) == 0 {
                    return v_x_1891_;
                } else {
                    v_head_1893_ = crate::leanh::lean_ctor_get(v_x_1892_, 0);
                    v_tail_1894_ = crate::leanh::lean_ctor_get(v_x_1892_, 1);
                    v_isSharedCheck_1916_ = (!crate::leanh::lean_is_exclusive(v_x_1892_)) as u8;
                    if v_isSharedCheck_1916_ == 0 {
                        v___x_1896_ = v_x_1892_;
                        v_isShared_1897_ = v_isSharedCheck_1916_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1894_);
                        crate::leanh::lean_inc(v_head_1893_);
                        crate::leanh::lean_dec(v_x_1892_);
                        v___x_1896_ = crate::leanh::lean_box(0);
                        v_isShared_1897_ = v_isSharedCheck_1916_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1898_ = crate::leanh::lean_ctor_get(v_head_1893_, 0);
                v_isSharedCheck_1914_ = (!crate::leanh::lean_is_exclusive(v_head_1893_)) as u8;
                if v_isSharedCheck_1914_ == 0 {
                    v_unused_1915_ = crate::leanh::lean_ctor_get(v_head_1893_, 1);
                    crate::leanh::lean_dec(v_unused_1915_);
                    v___x_1900_ = v_head_1893_;
                    v_isShared_1901_ = v_isSharedCheck_1914_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1898_);
                    crate::leanh::lean_dec(v_head_1893_);
                    v___x_1900_ = crate::leanh::lean_box(0);
                    v_isShared_1901_ = v_isSharedCheck_1914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
                if v_isShared_1901_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1900_, 7);
                    crate::leanh::lean_ctor_set(v___x_1900_, 1, v___x_1902_);
                    crate::leanh::lean_ctor_set(v___x_1900_, 0, v_x_1891_);
                    v___x_1904_ = v___x_1900_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_x_1891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1902_);
                    v___x_1904_ = v_reuseFailAlloc_1913_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1905_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3);
                if v_isShared_1897_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1896_, 7);
                    crate::leanh::lean_ctor_set(v___x_1896_, 1, v___x_1905_);
                    crate::leanh::lean_ctor_set(v___x_1896_, 0, v___x_1904_);
                    v___x_1907_ = v___x_1896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1904_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1905_);
                    v___x_1907_ = v_reuseFailAlloc_1912_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1908_ = l_Lean_MessageData_ofSyntax(v_before_1898_);
                v___x_1909_ = l_Lean_indentD(v___x_1908_);
                v___x_1910_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1910_, 0, v___x_1907_);
                crate::leanh::lean_ctor_set(v___x_1910_, 1, v___x_1909_);
                v_x_1891_ = v___x_1910_;
                v_x_1892_ = v_tail_1894_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(
    mut v_opts_1917_: *mut crate::leanh::LeanObject,
    mut v_opt_1918_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1919_ = crate::leanh::lean_ctor_get(v_opt_1918_, 0);
    v_defValue_1920_ = crate::leanh::lean_ctor_get(v_opt_1918_, 1);
    v_map_1921_ = crate::leanh::lean_ctor_get(v_opts_1917_, 0);
    v___x_1922_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1921_,
            v_name_1919_,
        );
    if crate::leanh::lean_obj_tag(v___x_1922_) == 0 {
        let mut v___x_1923_: u8 = 0;
        v___x_1923_ = (crate::leanh::lean_unbox(v_defValue_1920_) as u8);
        return v___x_1923_;
    } else {
        let mut v_val_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1924_ = crate::leanh::lean_ctor_get(v___x_1922_, 0);
        crate::leanh::lean_inc(v_val_1924_);
        crate::leanh::lean_dec_ref_known(v___x_1922_, 1);
        if crate::leanh::lean_obj_tag(v_val_1924_) == 1 {
            let mut v_v_1925_: u8 = 0;
            v_v_1925_ = crate::leanh::lean_ctor_get_uint8(v_val_1924_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1924_, 0);
            return v_v_1925_;
        } else {
            let mut v___x_1926_: u8 = 0;
            crate::leanh::lean_dec(v_val_1924_);
            v___x_1926_ = (crate::leanh::lean_unbox(v_defValue_1920_) as u8);
            return v___x_1926_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(
    mut v_opts_1927_: *mut crate::leanh::LeanObject,
    mut v_opt_1928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1929_: u8 = 0;
    let mut v_r_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_1927_, v_opt_1928_);
    crate::leanh::lean_dec_ref(v_opt_1928_);
    crate::leanh::lean_dec_ref(v_opts_1927_);
    v_r_1930_ = crate::leanh::lean_box((v_res_1929_) as usize);
    return v_r_1930_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1;
    v___x_1935_ = l_Lean_MessageData_ofFormat(v___x_1934_);
    return v___x_1935_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(
    mut v_msgData_1936_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1937_: *mut crate::leanh::LeanObject,
    mut v___y_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_unused_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1940_ = lean_st_ref_get(v___y_1938_);
                v_scopes_1941_ = crate::leanh::lean_ctor_get(v___x_1940_, 2);
                crate::leanh::lean_inc(v_scopes_1941_);
                crate::leanh::lean_dec(v___x_1940_);
                v___x_1942_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1943_ = l_List_head_x21___redArg(v___x_1942_, v_scopes_1941_);
                crate::leanh::lean_dec(v_scopes_1941_);
                v_opts_1944_ = crate::leanh::lean_ctor_get(v___x_1943_, 1);
                crate::leanh::lean_inc_ref(v_opts_1944_);
                crate::leanh::lean_dec(v___x_1943_);
                v___x_1945_ = l_Lean_Elab_pp_macroStack;
                v___x_1946_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_1944_, v___x_1945_);
                crate::leanh::lean_dec_ref(v_opts_1944_);
                if v___x_1946_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1937_);
                    v___x_1947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1947_, 0, v_msgData_1936_);
                    return v___x_1947_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1937_) == 0 {
                        v___x_1948_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1948_, 0, v_msgData_1936_);
                        return v___x_1948_;
                    } else {
                        v_head_1949_ = crate::leanh::lean_ctor_get(v_macroStack_1937_, 0);
                        crate::leanh::lean_inc(v_head_1949_);
                        v_after_1950_ = crate::leanh::lean_ctor_get(v_head_1949_, 1);
                        v_isSharedCheck_1965_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1949_)) as u8;
                        if v_isSharedCheck_1965_ == 0 {
                            v_unused_1966_ = crate::leanh::lean_ctor_get(v_head_1949_, 0);
                            crate::leanh::lean_dec(v_unused_1966_);
                            v___x_1952_ = v_head_1949_;
                            v_isShared_1953_ = v_isSharedCheck_1965_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1950_);
                            crate::leanh::lean_dec(v_head_1949_);
                            v___x_1952_ = crate::leanh::lean_box(0);
                            v_isShared_1953_ = v_isSharedCheck_1965_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
                if v_isShared_1953_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1952_, 7);
                    crate::leanh::lean_ctor_set(v___x_1952_, 1, v___x_1954_);
                    crate::leanh::lean_ctor_set(v___x_1952_, 0, v_msgData_1936_);
                    v___x_1956_ = v___x_1952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_msgData_1936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1954_);
                    v___x_1956_ = v_reuseFailAlloc_1964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1957_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2);
                v___x_1958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1958_, 0, v___x_1956_);
                crate::leanh::lean_ctor_set(v___x_1958_, 1, v___x_1957_);
                v___x_1959_ = l_Lean_MessageData_ofSyntax(v_after_1950_);
                v___x_1960_ = l_Lean_indentD(v___x_1959_);
                v_msgData_1961_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1961_, 0, v___x_1958_);
                crate::leanh::lean_ctor_set(v_msgData_1961_, 1, v___x_1960_);
                v___x_1962_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(v_msgData_1961_, v_macroStack_1937_);
                v___x_1963_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1963_, 0, v___x_1962_);
                return v___x_1963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_msgData_1967_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1968_: *mut crate::leanh::LeanObject,
    mut v___y_1969_: *mut crate::leanh::LeanObject,
    mut v___y_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1967_, v_macroStack_1968_, v___y_1969_);
    crate::leanh::lean_dec(v___y_1969_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(
    mut v_msg_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_a_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1976_ = l_Lean_Elab_Command_getRef___redArg(v___y_1973_);
                if crate::leanh::lean_obj_tag(v___x_1976_) == 0 {
                    v_a_1977_ = crate::leanh::lean_ctor_get(v___x_1976_, 0);
                    crate::leanh::lean_inc(v_a_1977_);
                    crate::leanh::lean_dec_ref_known(v___x_1976_, 1);
                    v_macroStack_1978_ = crate::leanh::lean_ctor_get(v___y_1973_, 4);
                    v___x_1979_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_1972_, v___y_1974_);
                    v_a_1980_ = crate::leanh::lean_ctor_get(v___x_1979_, 0);
                    crate::leanh::lean_inc(v_a_1980_);
                    crate::leanh::lean_dec_ref(v___x_1979_);
                    v___x_1981_ = l_Lean_Elab_getBetterRef(v_a_1977_, v_macroStack_1978_);
                    crate::leanh::lean_dec(v_a_1977_);
                    crate::leanh::lean_inc(v_macroStack_1978_);
                    v___x_1982_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_a_1980_, v_macroStack_1978_, v___y_1974_);
                    v_a_1983_ = crate::leanh::lean_ctor_get(v___x_1982_, 0);
                    v_isSharedCheck_1991_ = (!crate::leanh::lean_is_exclusive(v___x_1982_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1985_ = v___x_1982_;
                        v_isShared_1986_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1983_);
                        crate::leanh::lean_dec(v___x_1982_);
                        v___x_1985_ = crate::leanh::lean_box(0);
                        v_isShared_1986_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1972_);
                    v_a_1992_ = crate::leanh::lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_1999_ = (!crate::leanh::lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_1999_ == 0 {
                        v___x_1994_ = v___x_1976_;
                        v_isShared_1995_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1992_);
                        crate::leanh::lean_dec(v___x_1976_);
                        v___x_1994_ = crate::leanh::lean_box(0);
                        v_isShared_1995_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1987_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1987_, 0, v___x_1981_);
                crate::leanh::lean_ctor_set(v___x_1987_, 1, v_a_1983_);
                if v_isShared_1986_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1985_, 1);
                    crate::leanh::lean_ctor_set(v___x_1985_, 0, v___x_1987_);
                    v___x_1989_ = v___x_1985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
                    v___x_1989_ = v_reuseFailAlloc_1990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1989_;
            }
            3 => {
                if v_isShared_1995_ == 0 {
                    v___x_1997_ = v___x_1994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_1998_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg___boxed(
    mut v_msg_2000_: *mut crate::leanh::LeanObject,
    mut v___y_2001_: *mut crate::leanh::LeanObject,
    mut v___y_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2004_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_2000_, v___y_2001_, v___y_2002_);
    crate::leanh::lean_dec(v___y_2002_);
    crate::leanh::lean_dec_ref(v___y_2001_);
    return v_res_2004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(
    mut v_ref_2005_: *mut crate::leanh::LeanObject,
    mut v_msg_2006_: *mut crate::leanh::LeanObject,
    mut v___y_2007_: *mut crate::leanh::LeanObject,
    mut v___y_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2021_: u8 = 0;
    let mut v_ref_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2010_ = l_Lean_Elab_Command_getRef___redArg(v___y_2007_);
                if crate::leanh::lean_obj_tag(v___x_2010_) == 0 {
                    v_a_2011_ = crate::leanh::lean_ctor_get(v___x_2010_, 0);
                    crate::leanh::lean_inc(v_a_2011_);
                    crate::leanh::lean_dec_ref_known(v___x_2010_, 1);
                    v_fileName_2012_ = crate::leanh::lean_ctor_get(v___y_2007_, 0);
                    v_fileMap_2013_ = crate::leanh::lean_ctor_get(v___y_2007_, 1);
                    v_currRecDepth_2014_ = crate::leanh::lean_ctor_get(v___y_2007_, 2);
                    v_cmdPos_2015_ = crate::leanh::lean_ctor_get(v___y_2007_, 3);
                    v_macroStack_2016_ = crate::leanh::lean_ctor_get(v___y_2007_, 4);
                    v_quotContext_x3f_2017_ = crate::leanh::lean_ctor_get(v___y_2007_, 5);
                    v_currMacroScope_2018_ = crate::leanh::lean_ctor_get(v___y_2007_, 6);
                    v_snap_x3f_2019_ = crate::leanh::lean_ctor_get(v___y_2007_, 8);
                    v_cancelTk_x3f_2020_ = crate::leanh::lean_ctor_get(v___y_2007_, 9);
                    v_suppressElabErrors_2021_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2007_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_2022_ = l_Lean_replaceRef(v_ref_2005_, v_a_2011_);
                    crate::leanh::lean_dec(v_a_2011_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2020_);
                    crate::leanh::lean_inc(v_snap_x3f_2019_);
                    crate::leanh::lean_inc(v_currMacroScope_2018_);
                    crate::leanh::lean_inc(v_quotContext_x3f_2017_);
                    crate::leanh::lean_inc(v_macroStack_2016_);
                    crate::leanh::lean_inc(v_cmdPos_2015_);
                    crate::leanh::lean_inc(v_currRecDepth_2014_);
                    crate::leanh::lean_inc_ref(v_fileMap_2013_);
                    crate::leanh::lean_inc_ref(v_fileName_2012_);
                    v___x_2023_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2023_, 0, v_fileName_2012_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 1, v_fileMap_2013_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 2, v_currRecDepth_2014_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 3, v_cmdPos_2015_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 4, v_macroStack_2016_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 5, v_quotContext_x3f_2017_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 6, v_currMacroScope_2018_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 7, v_ref_2022_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 8, v_snap_x3f_2019_);
                    crate::leanh::lean_ctor_set(v___x_2023_, 9, v_cancelTk_x3f_2020_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2023_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2021_,
                    );
                    v___x_2024_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_2006_, v___x_2023_, v___y_2008_);
                    crate::leanh::lean_dec_ref_known(v___x_2023_, 10);
                    return v___x_2024_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2006_);
                    v_a_2025_ = crate::leanh::lean_ctor_get(v___x_2010_, 0);
                    v_isSharedCheck_2032_ = (!crate::leanh::lean_is_exclusive(v___x_2010_)) as u8;
                    if v_isSharedCheck_2032_ == 0 {
                        v___x_2027_ = v___x_2010_;
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2025_);
                        crate::leanh::lean_dec(v___x_2010_);
                        v___x_2027_ = crate::leanh::lean_box(0);
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2028_ == 0 {
                    v___x_2030_ = v___x_2027_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
                    v___x_2030_ = v_reuseFailAlloc_2031_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg___boxed(
    mut v_ref_2033_: *mut crate::leanh::LeanObject,
    mut v_msg_2034_: *mut crate::leanh::LeanObject,
    mut v___y_2035_: *mut crate::leanh::LeanObject,
    mut v___y_2036_: *mut crate::leanh::LeanObject,
    mut v___y_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_2033_, v_msg_2034_, v___y_2035_, v___y_2036_);
    crate::leanh::lean_dec(v___y_2036_);
    crate::leanh::lean_dec_ref(v___y_2035_);
    crate::leanh::lean_dec(v_ref_2033_);
    return v_res_2038_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_2044_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23;
    v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
    return v___x_2073_;
}
pub unsafe fn l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(
    mut v_tyName_2101_: *mut crate::leanh::LeanObject,
    mut v_id_2102_: *mut crate::leanh::LeanObject,
    mut v_ty_2103_: *mut crate::leanh::LeanObject,
    mut v_config_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v_a_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_whereInfo_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fs_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldMap_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_whereTk_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fs_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: u8 = 0;
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fs_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2193_ = l_Lake_PackageConfig_instConfigInfo;
                v___x_2226_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22;
                crate::leanh::lean_inc(v_config_2104_);
                v___x_2227_ = l_Lean_Syntax_isOfKind(v_config_2104_, v___x_2226_);
                if v___x_2227_ == 0 {
                    crate::leanh::lean_dec(v_ty_2103_);
                    crate::leanh::lean_dec(v_id_2102_);
                    crate::leanh::lean_dec(v_tyName_2101_);
                    v___x_2228_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                    v___x_2229_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2228_, v_a_2105_, v_a_2106_);
                    crate::leanh::lean_dec(v_config_2104_);
                    return v___x_2229_;
                } else {
                    v___x_2230_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2231_ = l_Lean_Syntax_getArg(v_config_2104_, v___x_2230_);
                    crate::leanh::lean_inc(v___x_2231_);
                    v___x_2232_ = l_Lean_Syntax_matchesNull(v___x_2231_, v___x_2230_);
                    if v___x_2232_ == 0 {
                        v___x_2233_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_2231_);
                        v___x_2234_ = l_Lean_Syntax_matchesNull(v___x_2231_, v___x_2233_);
                        if v___x_2234_ == 0 {
                            crate::leanh::lean_dec(v___x_2231_);
                            crate::leanh::lean_dec(v_ty_2103_);
                            crate::leanh::lean_dec(v_id_2102_);
                            crate::leanh::lean_dec(v_tyName_2101_);
                            v___x_2235_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                            v___x_2236_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2235_, v_a_2105_, v_a_2106_);
                            crate::leanh::lean_dec(v_config_2104_);
                            return v___x_2236_;
                        } else {
                            v___x_2237_ = l_Lean_Syntax_getArg(v___x_2231_, v___x_2230_);
                            crate::leanh::lean_dec(v___x_2231_);
                            v___x_2238_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26;
                            crate::leanh::lean_inc(v___x_2237_);
                            v___x_2239_ = l_Lean_Syntax_isOfKind(v___x_2237_, v___x_2238_);
                            if v___x_2239_ == 0 {
                                v___x_2240_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28;
                                crate::leanh::lean_inc(v___x_2237_);
                                v___x_2241_ = l_Lean_Syntax_isOfKind(v___x_2237_, v___x_2240_);
                                if v___x_2241_ == 0 {
                                    crate::leanh::lean_dec(v___x_2237_);
                                    crate::leanh::lean_dec(v_ty_2103_);
                                    crate::leanh::lean_dec(v_id_2102_);
                                    crate::leanh::lean_dec(v_tyName_2101_);
                                    v___x_2242_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                    v___x_2243_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2242_, v_a_2105_, v_a_2106_);
                                    crate::leanh::lean_dec(v_config_2104_);
                                    return v___x_2243_;
                                } else {
                                    v___x_2244_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2230_);
                                    v___x_2245_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30;
                                    crate::leanh::lean_inc(v___x_2244_);
                                    v___x_2246_ = l_Lean_Syntax_isOfKind(v___x_2244_, v___x_2245_);
                                    if v___x_2246_ == 0 {
                                        crate::leanh::lean_dec(v___x_2244_);
                                        crate::leanh::lean_dec(v___x_2237_);
                                        crate::leanh::lean_dec(v_ty_2103_);
                                        crate::leanh::lean_dec(v_id_2102_);
                                        crate::leanh::lean_dec(v_tyName_2101_);
                                        v___x_2247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                        v___x_2248_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2247_, v_a_2105_, v_a_2106_);
                                        crate::leanh::lean_dec(v_config_2104_);
                                        return v___x_2248_;
                                    } else {
                                        v___x_2249_ =
                                            l_Lean_Syntax_getArg(v___x_2244_, v___x_2233_);
                                        v___x_2250_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32;
                                        crate::leanh::lean_inc(v___x_2249_);
                                        v___x_2251_ =
                                            l_Lean_Syntax_isOfKind(v___x_2249_, v___x_2250_);
                                        if v___x_2251_ == 0 {
                                            crate::leanh::lean_dec(v___x_2249_);
                                            crate::leanh::lean_dec(v___x_2244_);
                                            crate::leanh::lean_dec(v___x_2237_);
                                            crate::leanh::lean_dec(v_ty_2103_);
                                            crate::leanh::lean_dec(v_id_2102_);
                                            crate::leanh::lean_dec(v_tyName_2101_);
                                            v___x_2252_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                            v___x_2253_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2252_, v_a_2105_, v_a_2106_);
                                            crate::leanh::lean_dec(v_config_2104_);
                                            return v___x_2253_;
                                        } else {
                                            v_tk_2254_ =
                                                l_Lean_Syntax_getArg(v___x_2244_, v___x_2230_);
                                            crate::leanh::lean_dec(v___x_2244_);
                                            v___x_2255_ =
                                                l_Lean_Syntax_getArg(v___x_2249_, v___x_2230_);
                                            crate::leanh::lean_dec(v___x_2249_);
                                            v___x_2263_ =
                                                l_Lean_Syntax_getArg(v___x_2237_, v___x_2233_);
                                            crate::leanh::lean_dec(v___x_2237_);
                                            v___x_2264_ = l_Lean_Syntax_isNone(v___x_2263_);
                                            if v___x_2264_ == 0 {
                                                crate::leanh::lean_inc(v___x_2263_);
                                                v___x_2265_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2263_,
                                                    v___x_2233_,
                                                );
                                                if v___x_2265_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2263_);
                                                    crate::leanh::lean_dec(v___x_2255_);
                                                    crate::leanh::lean_dec(v_tk_2254_);
                                                    crate::leanh::lean_dec(v_ty_2103_);
                                                    crate::leanh::lean_dec(v_id_2102_);
                                                    crate::leanh::lean_dec(v_tyName_2101_);
                                                    v___x_2266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                                    v___x_2267_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2266_, v_a_2105_, v_a_2106_);
                                                    crate::leanh::lean_dec(v_config_2104_);
                                                    return v___x_2267_;
                                                } else {
                                                    v_wds_x3f_2268_ = l_Lean_Syntax_getArg(
                                                        v___x_2263_,
                                                        v___x_2230_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_2263_);
                                                    v___x_2269_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                                    crate::leanh::lean_inc(v_wds_x3f_2268_);
                                                    v___x_2270_ = l_Lean_Syntax_isOfKind(
                                                        v_wds_x3f_2268_,
                                                        v___x_2269_,
                                                    );
                                                    if v___x_2270_ == 0 {
                                                        crate::leanh::lean_dec(v_wds_x3f_2268_);
                                                        crate::leanh::lean_dec(v___x_2255_);
                                                        crate::leanh::lean_dec(v_tk_2254_);
                                                        crate::leanh::lean_dec(v_ty_2103_);
                                                        crate::leanh::lean_dec(v_id_2102_);
                                                        crate::leanh::lean_dec(v_tyName_2101_);
                                                        v___x_2271_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                                        v___x_2272_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2271_, v_a_2105_, v_a_2106_);
                                                        crate::leanh::lean_dec(v_config_2104_);
                                                        return v___x_2272_;
                                                    } else {
                                                        v___x_2273_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            1,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2273_,
                                                            0,
                                                            v_wds_x3f_2268_,
                                                        );
                                                        v_wds_x3f_2257_ = v___x_2273_;
                                                        v___y_2258_ = v_a_2105_;
                                                        v___y_2259_ = v_a_2106_;
                                                        state = 12;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v___x_2263_);
                                                v___x_2274_ = crate::leanh::lean_box(0);
                                                v_wds_x3f_2257_ = v___x_2274_;
                                                v___y_2258_ = v_a_2105_;
                                                v___y_2259_ = v_a_2106_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_2275_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2233_);
                                v___x_2276_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32;
                                crate::leanh::lean_inc(v___x_2275_);
                                v___x_2277_ = l_Lean_Syntax_isOfKind(v___x_2275_, v___x_2276_);
                                if v___x_2277_ == 0 {
                                    crate::leanh::lean_dec(v___x_2275_);
                                    crate::leanh::lean_dec(v___x_2237_);
                                    crate::leanh::lean_dec(v_ty_2103_);
                                    crate::leanh::lean_dec(v_id_2102_);
                                    crate::leanh::lean_dec(v_tyName_2101_);
                                    v___x_2278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                    v___x_2279_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2278_, v_a_2105_, v_a_2106_);
                                    crate::leanh::lean_dec(v_config_2104_);
                                    return v___x_2279_;
                                } else {
                                    v_tk_2280_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2230_);
                                    v___x_2281_ = l_Lean_Syntax_getArg(v___x_2275_, v___x_2230_);
                                    crate::leanh::lean_dec(v___x_2275_);
                                    v___x_2289_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_2290_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2289_);
                                    crate::leanh::lean_dec(v___x_2237_);
                                    v___x_2291_ = l_Lean_Syntax_isNone(v___x_2290_);
                                    if v___x_2291_ == 0 {
                                        crate::leanh::lean_inc(v___x_2290_);
                                        v___x_2292_ =
                                            l_Lean_Syntax_matchesNull(v___x_2290_, v___x_2233_);
                                        if v___x_2292_ == 0 {
                                            crate::leanh::lean_dec(v___x_2290_);
                                            crate::leanh::lean_dec(v___x_2281_);
                                            crate::leanh::lean_dec(v_tk_2280_);
                                            crate::leanh::lean_dec(v_ty_2103_);
                                            crate::leanh::lean_dec(v_id_2102_);
                                            crate::leanh::lean_dec(v_tyName_2101_);
                                            v___x_2293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                            v___x_2294_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2293_, v_a_2105_, v_a_2106_);
                                            crate::leanh::lean_dec(v_config_2104_);
                                            return v___x_2294_;
                                        } else {
                                            v_wds_x3f_2295_ =
                                                l_Lean_Syntax_getArg(v___x_2290_, v___x_2230_);
                                            crate::leanh::lean_dec(v___x_2290_);
                                            v___x_2296_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                            crate::leanh::lean_inc(v_wds_x3f_2295_);
                                            v___x_2297_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_2295_,
                                                v___x_2296_,
                                            );
                                            if v___x_2297_ == 0 {
                                                crate::leanh::lean_dec(v_wds_x3f_2295_);
                                                crate::leanh::lean_dec(v___x_2281_);
                                                crate::leanh::lean_dec(v_tk_2280_);
                                                crate::leanh::lean_dec(v_ty_2103_);
                                                crate::leanh::lean_dec(v_id_2102_);
                                                crate::leanh::lean_dec(v_tyName_2101_);
                                                v___x_2298_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                                v___x_2299_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2298_, v_a_2105_, v_a_2106_);
                                                crate::leanh::lean_dec(v_config_2104_);
                                                return v___x_2299_;
                                            } else {
                                                v___x_2300_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2300_,
                                                    0,
                                                    v_wds_x3f_2295_,
                                                );
                                                v_wds_x3f_2283_ = v___x_2300_;
                                                v___y_2284_ = v_a_2105_;
                                                v___y_2285_ = v_a_2106_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_2290_);
                                        v___x_2301_ = crate::leanh::lean_box(0);
                                        v_wds_x3f_2283_ = v___x_2301_;
                                        v___y_2284_ = v_a_2105_;
                                        v___y_2285_ = v_a_2106_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2231_);
                        v___x_2302_ = crate::leanh::lean_box(2);
                        v___x_2303_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8;
                        v___x_2304_ = crate::leanh::lean_box(0);
                        v_whereInfo_2195_ = v___x_2302_;
                        v_fs_2196_ = v___x_2303_;
                        v_wds_x3f_2197_ = v___x_2304_;
                        v___y_2198_ = v_a_2105_;
                        v___y_2199_ = v_a_2106_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2117_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_2116_, 5);
                crate::leanh::lean_inc_ref_n(v___y_2115_, 6);
                crate::leanh::lean_inc_ref_n(v___y_2111_, 6);
                v___x_2118_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2117_);
                v___x_2119_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1;
                v___x_2120_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2119_);
                v___x_2121_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                v___x_2122_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                crate::leanh::lean_inc_n(v___y_2109_, 8);
                v___x_2123_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2123_, 0, v___y_2109_);
                crate::leanh::lean_ctor_set(v___x_2123_, 1, v___x_2121_);
                crate::leanh::lean_ctor_set(v___x_2123_, 2, v___x_2122_);
                crate::leanh::lean_inc_ref_n(v___x_2123_, 8);
                v___x_2124_ = l_Lean_Syntax_node7(
                    v___y_2109_,
                    v___x_2120_,
                    v___x_2123_,
                    v___x_2123_,
                    v___x_2123_,
                    v___x_2123_,
                    v___x_2123_,
                    v___x_2123_,
                    v___x_2123_,
                );
                v___x_2125_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5;
                v___x_2126_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2125_);
                v___x_2127_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6;
                v___x_2128_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2128_, 0, v___y_2109_);
                crate::leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                v___x_2129_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7;
                v___x_2130_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2129_);
                v___x_2131_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8;
                crate::leanh::lean_inc_n(v___y_2114_, 2);
                v___x_2132_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2132_, 0, v___y_2114_);
                crate::leanh::lean_ctor_set(v___x_2132_, 1, v___x_2121_);
                crate::leanh::lean_ctor_set(v___x_2132_, 2, v___x_2131_);
                v___x_2133_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
                v___x_2135_ = lean_array_push(v___x_2134_, v_id_2102_);
                v___x_2136_ = lean_array_push(v___x_2135_, v___x_2132_);
                v___x_2137_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2137_, 0, v___y_2114_);
                crate::leanh::lean_ctor_set(v___x_2137_, 1, v___x_2130_);
                crate::leanh::lean_ctor_set(v___x_2137_, 2, v___x_2136_);
                v___x_2138_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9;
                v___x_2139_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2138_);
                v___x_2140_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10;
                v___x_2141_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11;
                v___x_2142_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___x_2140_, v___x_2141_);
                v___x_2143_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12;
                v___x_2144_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2144_, 0, v___y_2109_);
                crate::leanh::lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                v___x_2145_ =
                    l_Lean_Syntax_node2(v___y_2109_, v___x_2142_, v___x_2144_, v_ty_2103_);
                v___x_2146_ = l_Lean_Syntax_node1(v___y_2109_, v___x_2121_, v___x_2145_);
                v___x_2147_ =
                    l_Lean_Syntax_node2(v___y_2109_, v___x_2139_, v___x_2123_, v___x_2146_);
                v___x_2148_ = l_Lean_Syntax_node5(
                    v___y_2109_,
                    v___x_2126_,
                    v___x_2128_,
                    v___x_2137_,
                    v___x_2147_,
                    v___y_2110_,
                    v___x_2123_,
                );
                v___x_2149_ =
                    l_Lean_Syntax_node2(v___y_2109_, v___x_2118_, v___x_2124_, v___x_2148_);
                crate::leanh::lean_inc(v___x_2149_);
                v___x_2150_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_2150_, 0, v___x_2149_);
                v___x_2151_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                    v_config_2104_,
                    v___x_2149_,
                    v___x_2150_,
                    v___y_2113_,
                    v___y_2112_,
                );
                return v___x_2151_;
            }
            2 => {
                v___x_2162_ = l_Lean_Elab_Command_getRef___redArg(v___y_2157_);
                if crate::leanh::lean_obj_tag(v___x_2162_) == 0 {
                    v_a_2163_ = crate::leanh::lean_ctor_get(v___x_2162_, 0);
                    crate::leanh::lean_inc(v_a_2163_);
                    crate::leanh::lean_dec_ref_known(v___x_2162_, 1);
                    v___x_2164_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2157_);
                    if crate::leanh::lean_obj_tag(v___x_2164_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2164_, 1);
                        v_quotContext_x3f_2165_ = crate::leanh::lean_ctor_get(v___y_2157_, 5);
                        v___x_2166_ = l_Lean_mkOptionalNode(v___y_2161_);
                        v___x_2167_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_2168_ = lean_mk_empty_array_with_capacity(v___x_2167_);
                        v___x_2169_ = lean_array_push(v___x_2168_, v___y_2160_);
                        v___x_2170_ = lean_array_push(v___x_2169_, v___y_2156_);
                        v___x_2171_ = lean_array_push(v___x_2170_, v___x_2166_);
                        v___x_2172_ = crate::leanh::lean_box(2);
                        crate::leanh::lean_inc(v___y_2153_);
                        v___x_2173_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2173_, 0, v___x_2172_);
                        crate::leanh::lean_ctor_set(v___x_2173_, 1, v___y_2153_);
                        crate::leanh::lean_ctor_set(v___x_2173_, 2, v___x_2171_);
                        v___x_2174_ = 0;
                        v___x_2175_ = l_Lean_SourceInfo_fromRef(v_a_2163_, v___x_2174_);
                        crate::leanh::lean_dec(v_a_2163_);
                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_2165_) == 0 {
                            v___x_2176_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2155_);
                            crate::leanh::lean_dec_ref(v___x_2176_);
                            v___y_2109_ = v___x_2175_;
                            v___y_2110_ = v___x_2173_;
                            v___y_2111_ = v___y_2154_;
                            v___y_2112_ = v___y_2155_;
                            v___y_2113_ = v___y_2157_;
                            v___y_2114_ = v___x_2172_;
                            v___y_2115_ = v___y_2158_;
                            v___y_2116_ = v___y_2159_;
                            state = 1;
                            continue;
                        } else {
                            v___y_2109_ = v___x_2175_;
                            v___y_2110_ = v___x_2173_;
                            v___y_2111_ = v___y_2154_;
                            v___y_2112_ = v___y_2155_;
                            v___y_2113_ = v___y_2157_;
                            v___y_2114_ = v___x_2172_;
                            v___y_2115_ = v___y_2158_;
                            v___y_2116_ = v___y_2159_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2163_);
                        crate::leanh::lean_dec(v___y_2161_);
                        crate::leanh::lean_dec(v___y_2160_);
                        crate::leanh::lean_dec(v___y_2156_);
                        crate::leanh::lean_dec(v_config_2104_);
                        crate::leanh::lean_dec(v_ty_2103_);
                        crate::leanh::lean_dec(v_id_2102_);
                        v_a_2177_ = crate::leanh::lean_ctor_get(v___x_2164_, 0);
                        v_isSharedCheck_2184_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2164_)) as u8;
                        if v_isSharedCheck_2184_ == 0 {
                            v___x_2179_ = v___x_2164_;
                            v_isShared_2180_ = v_isSharedCheck_2184_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2177_);
                            crate::leanh::lean_dec(v___x_2164_);
                            v___x_2179_ = crate::leanh::lean_box(0);
                            v_isShared_2180_ = v_isSharedCheck_2184_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2161_);
                    crate::leanh::lean_dec(v___y_2160_);
                    crate::leanh::lean_dec(v___y_2156_);
                    crate::leanh::lean_dec(v_config_2104_);
                    crate::leanh::lean_dec(v_ty_2103_);
                    crate::leanh::lean_dec(v_id_2102_);
                    v_a_2185_ = crate::leanh::lean_ctor_get(v___x_2162_, 0);
                    v_isSharedCheck_2192_ = (!crate::leanh::lean_is_exclusive(v___x_2162_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v___x_2187_ = v___x_2162_;
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2185_);
                        crate::leanh::lean_dec(v___x_2162_);
                        v___x_2187_ = crate::leanh::lean_box(0);
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2180_ == 0 {
                    v___x_2182_ = v___x_2179_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2183_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
                    v___x_2182_ = v_reuseFailAlloc_2183_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2182_;
            }
            5 => {
                if v_isShared_2188_ == 0 {
                    v___x_2190_ = v___x_2187_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2190_;
            }
            7 => {
                v_fieldMap_2200_ = crate::leanh::lean_ctor_get(v___x_2193_, 1);
                v___x_2201_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(
                    v_tyName_2101_,
                    v_fieldMap_2200_,
                    v_fs_2196_,
                    v___y_2198_,
                    v___y_2199_,
                );
                crate::leanh::lean_dec_ref(v_fs_2196_);
                if crate::leanh::lean_obj_tag(v___x_2201_) == 0 {
                    v_a_2202_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                    crate::leanh::lean_inc(v_a_2202_);
                    crate::leanh::lean_dec_ref_known(v___x_2201_, 1);
                    v___x_2203_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13;
                    v_whereTk_2204_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_whereTk_2204_, 0, v_whereInfo_2195_);
                    crate::leanh::lean_ctor_set(v_whereTk_2204_, 1, v___x_2203_);
                    v___x_2205_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                    v___x_2206_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15;
                    v___x_2207_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                    v___x_2208_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18;
                    if crate::leanh::lean_obj_tag(v_wds_x3f_2197_) == 0 {
                        v___x_2209_ = crate::leanh::lean_box(0);
                        v___y_2153_ = v___x_2208_;
                        v___y_2154_ = v___x_2205_;
                        v___y_2155_ = v___y_2199_;
                        v___y_2156_ = v_a_2202_;
                        v___y_2157_ = v___y_2198_;
                        v___y_2158_ = v___x_2206_;
                        v___y_2159_ = v___x_2207_;
                        v___y_2160_ = v_whereTk_2204_;
                        v___y_2161_ = v___x_2209_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2210_ = crate::leanh::lean_ctor_get(v_wds_x3f_2197_, 0);
                        v_isSharedCheck_2217_ =
                            (!crate::leanh::lean_is_exclusive(v_wds_x3f_2197_)) as u8;
                        if v_isSharedCheck_2217_ == 0 {
                            v___x_2212_ = v_wds_x3f_2197_;
                            v_isShared_2213_ = v_isSharedCheck_2217_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2210_);
                            crate::leanh::lean_dec(v_wds_x3f_2197_);
                            v___x_2212_ = crate::leanh::lean_box(0);
                            v_isShared_2213_ = v_isSharedCheck_2217_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_wds_x3f_2197_);
                    crate::leanh::lean_dec(v_whereInfo_2195_);
                    crate::leanh::lean_dec(v_config_2104_);
                    crate::leanh::lean_dec(v_ty_2103_);
                    crate::leanh::lean_dec(v_id_2102_);
                    v_a_2218_ = crate::leanh::lean_ctor_get(v___x_2201_, 0);
                    v_isSharedCheck_2225_ = (!crate::leanh::lean_is_exclusive(v___x_2201_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2220_ = v___x_2201_;
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2218_);
                        crate::leanh::lean_dec(v___x_2201_);
                        v___x_2220_ = crate::leanh::lean_box(0);
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2213_ == 0 {
                    v___x_2215_ = v___x_2212_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_val_2210_);
                    v___x_2215_ = v_reuseFailAlloc_2216_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___y_2153_ = v___x_2208_;
                v___y_2154_ = v___x_2205_;
                v___y_2155_ = v___y_2199_;
                v___y_2156_ = v_a_2202_;
                v___y_2157_ = v___y_2198_;
                v___y_2158_ = v___x_2206_;
                v___y_2159_ = v___x_2207_;
                v___y_2160_ = v_whereTk_2204_;
                v___y_2161_ = v___x_2215_;
                state = 2;
                continue;
            }
            10 => {
                if v_isShared_2221_ == 0 {
                    v___x_2223_ = v___x_2220_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2223_;
            }
            12 => {
                v_fs_2260_ = l_Lean_Syntax_getArgs(v___x_2255_);
                crate::leanh::lean_dec(v___x_2255_);
                v___x_2261_ = l_Lean_Syntax_getHeadInfo(v_tk_2254_);
                crate::leanh::lean_dec(v_tk_2254_);
                v___x_2262_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_2260_);
                crate::leanh::lean_dec_ref(v_fs_2260_);
                v_whereInfo_2195_ = v___x_2261_;
                v_fs_2196_ = v___x_2262_;
                v_wds_x3f_2197_ = v_wds_x3f_2257_;
                v___y_2198_ = v___y_2258_;
                v___y_2199_ = v___y_2259_;
                state = 7;
                continue;
            }
            13 => {
                v_fs_2286_ = l_Lean_Syntax_getArgs(v___x_2281_);
                crate::leanh::lean_dec(v___x_2281_);
                v___x_2287_ = l_Lean_Syntax_getHeadInfo(v_tk_2280_);
                crate::leanh::lean_dec(v_tk_2280_);
                v___x_2288_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_2286_);
                crate::leanh::lean_dec_ref(v_fs_2286_);
                v_whereInfo_2195_ = v___x_2287_;
                v_fs_2196_ = v___x_2288_;
                v_wds_x3f_2197_ = v_wds_x3f_2283_;
                v___y_2198_ = v___y_2284_;
                v___y_2199_ = v___y_2285_;
                state = 7;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___boxed(
    mut v_tyName_2305_: *mut crate::leanh::LeanObject,
    mut v_id_2306_: *mut crate::leanh::LeanObject,
    mut v_ty_2307_: *mut crate::leanh::LeanObject,
    mut v_config_2308_: *mut crate::leanh::LeanObject,
    mut v_a_2309_: *mut crate::leanh::LeanObject,
    mut v_a_2310_: *mut crate::leanh::LeanObject,
    mut v_a_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2312_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_2305_, v_id_2306_, v_ty_2307_, v_config_2308_, v_a_2309_, v_a_2310_);
    crate::leanh::lean_dec(v_a_2310_);
    crate::leanh::lean_dec_ref(v_a_2309_);
    return v_res_2312_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13;
    v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2341_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19;
    v___x_2342_ = l_String_toRawSubstring_x27(v___x_2341_);
    return v___x_2342_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34;
    v___x_2365_ = l_String_toRawSubstring_x27(v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2372_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40;
    v___x_2373_ = l_String_toRawSubstring_x27(v___x_2372_);
    return v___x_2373_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43;
    v___x_2378_ = l_String_toRawSubstring_x27(v___x_2377_);
    return v___x_2378_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46;
    v___x_2383_ = l_String_toRawSubstring_x27(v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2391_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53;
    v___x_2392_ = l_String_toRawSubstring_x27(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65;
    v___x_2413_ = l_String_toRawSubstring_x27(v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(
    mut v_stx_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: u8 = 0;
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v_a_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v___y_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2607_: u8 = 0;
    let mut v___y_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: u8 = 0;
    let mut v___y_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_a_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut v___y_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: u8 = 0;
    let mut v___y_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_a_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v___y_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2808_: u8 = 0;
    let mut v___y_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v___y_2859_: u8 = 0;
    let mut v___y_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2892_: u8 = 0;
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_kw_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2916_: u8 = 0;
    let mut v_ref_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_a_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_a_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2947_: u8 = 0;
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2951_: u8 = 0;
    let mut v___y_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_nameStx_x3f_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cfg_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nameStx_x3f_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2488_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12;
                crate::leanh::lean_inc(v_stx_2416_);
                v___x_2489_ = l_Lean_Syntax_isOfKind(v_stx_2416_, v___x_2488_);
                if v___x_2489_ == 0 {
                    v___x_2490_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
                    v___x_2491_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_2416_, v___x_2490_, v_a_2417_, v_a_2418_);
                    crate::leanh::lean_dec(v_stx_2416_);
                    return v___x_2491_;
                } else {
                    v___x_2492_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2493_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2492_);
                    v___x_2494_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2495_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2494_);
                    v___x_2496_ = crate::leanh::lean_unsigned_to_nat(2);
                    v_kw_2897_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2496_);
                    v___x_2984_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2985_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2984_);
                    v___x_2986_ = l_Lean_Syntax_isNone(v___x_2985_);
                    if v___x_2986_ == 0 {
                        crate::leanh::lean_inc(v___x_2985_);
                        v___x_2987_ = l_Lean_Syntax_matchesNull(v___x_2985_, v___x_2494_);
                        if v___x_2987_ == 0 {
                            crate::leanh::lean_dec(v___x_2985_);
                            crate::leanh::lean_dec(v_kw_2897_);
                            crate::leanh::lean_dec(v___x_2495_);
                            crate::leanh::lean_dec(v___x_2493_);
                            v___x_2988_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
                            v___x_2989_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_2416_, v___x_2988_, v_a_2417_, v_a_2418_);
                            crate::leanh::lean_dec(v_stx_2416_);
                            return v___x_2989_;
                        } else {
                            v_nameStx_x3f_2990_ = l_Lean_Syntax_getArg(v___x_2985_, v___x_2492_);
                            crate::leanh::lean_dec(v___x_2985_);
                            v___x_2991_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2991_, 0, v_nameStx_x3f_2990_);
                            v_nameStx_x3f_2969_ = v___x_2991_;
                            v___y_2970_ = v_a_2417_;
                            v___y_2971_ = v_a_2418_;
                            state = 36;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2985_);
                        v___x_2992_ = crate::leanh::lean_box(0);
                        v_nameStx_x3f_2969_ = v___x_2992_;
                        v___y_2970_ = v_a_2417_;
                        v___y_2971_ = v_a_2418_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_2432_);
                crate::leanh::lean_inc_n(v___y_2421_, 5);
                crate::leanh::lean_inc_n(v___y_2427_, 28);
                v___x_2445_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2445_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2445_, 1, v___y_2421_);
                crate::leanh::lean_ctor_set(v___x_2445_, 2, v___y_2432_);
                crate::leanh::lean_inc_ref(v___y_2444_);
                v___x_2446_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2446_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2446_, 1, v___y_2444_);
                crate::leanh::lean_inc_ref_n(v___x_2445_, 12);
                v___x_2447_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2425_, v___x_2445_);
                v___x_2448_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0;
                crate::leanh::lean_inc_ref(v___y_2433_);
                v___x_2449_ = l_Lean_Name_mkStr2(v___y_2433_, v___x_2448_);
                v___x_2450_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2450_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2450_, 1, v___x_2448_);
                v___x_2451_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2;
                v___x_2452_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3;
                v___x_2453_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2453_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2453_, 1, v___x_2452_);
                v___x_2454_ = l_Lean_Syntax_node1(v___y_2427_, v___x_2451_, v___x_2453_);
                v___x_2455_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2421_, v___x_2454_);
                v___x_2456_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4;
                v___x_2457_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2457_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2457_, 1, v___x_2456_);
                v___x_2458_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5;
                v___x_2459_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2459_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2459_, 1, v___x_2458_);
                crate::leanh::lean_inc_ref(v___y_2435_);
                v___x_2460_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2460_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2460_, 1, v___y_2435_);
                v___x_2461_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6;
                v___x_2462_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2462_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2462_, 1, v___x_2461_);
                v___x_2463_ = l_Lean_Syntax_node1(v___y_2427_, v___x_2451_, v___x_2462_);
                v___x_2464_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7;
                v___x_2465_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2465_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2465_, 1, v___x_2464_);
                crate::leanh::lean_inc_ref(v___x_2460_);
                v___x_2466_ = l_Lean_Syntax_node5(
                    v___y_2427_,
                    v___y_2421_,
                    v___x_2457_,
                    v___x_2459_,
                    v___x_2460_,
                    v___x_2463_,
                    v___x_2465_,
                );
                v___x_2467_ = l_Lean_Syntax_node4(
                    v___y_2427_,
                    v___x_2449_,
                    v___x_2450_,
                    v___x_2445_,
                    v___x_2455_,
                    v___x_2466_,
                );
                v___x_2468_ =
                    l_Lean_Syntax_node2(v___y_2427_, v___y_2441_, v___x_2447_, v___x_2467_);
                v___x_2469_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2421_, v___x_2468_);
                crate::leanh::lean_inc_ref(v___y_2424_);
                v___x_2470_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2470_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2470_, 1, v___y_2424_);
                v___x_2471_ = l_Lean_Syntax_node3(
                    v___y_2427_,
                    v___y_2434_,
                    v___x_2446_,
                    v___x_2469_,
                    v___x_2470_,
                );
                v___x_2472_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2421_, v___x_2471_);
                v___x_2473_ = l_Lean_Syntax_node7(
                    v___y_2427_,
                    v___y_2429_,
                    v___x_2445_,
                    v___x_2472_,
                    v___x_2445_,
                    v___x_2445_,
                    v___x_2445_,
                    v___x_2445_,
                    v___x_2445_,
                );
                v___x_2474_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2474_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2474_, 1, v___y_2438_);
                v___x_2475_ = lean_array_push(v___y_2422_, v___y_2430_);
                v___x_2476_ = lean_array_push(v___x_2475_, v___y_2431_);
                v___x_2477_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2477_, 0, v___y_2423_);
                crate::leanh::lean_ctor_set(v___x_2477_, 1, v___y_2443_);
                crate::leanh::lean_ctor_set(v___x_2477_, 2, v___x_2476_);
                v___x_2478_ =
                    l_Lean_Syntax_node2(v___y_2427_, v___y_2442_, v___x_2445_, v___x_2445_);
                v___x_2479_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9;
                v___x_2480_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10;
                v___x_2481_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2481_, 0, v___y_2427_);
                crate::leanh::lean_ctor_set(v___x_2481_, 1, v___x_2480_);
                v___x_2482_ = l_Lean_Syntax_node1(v___y_2427_, v___x_2479_, v___x_2481_);
                v___x_2483_ =
                    l_Lean_Syntax_node2(v___y_2427_, v___y_2428_, v___x_2445_, v___x_2445_);
                v___x_2484_ = l_Lean_Syntax_node4(
                    v___y_2427_,
                    v___y_2426_,
                    v___x_2460_,
                    v___x_2482_,
                    v___x_2483_,
                    v___x_2445_,
                );
                v___x_2485_ = l_Lean_Syntax_node4(
                    v___y_2427_,
                    v___y_2440_,
                    v___x_2474_,
                    v___x_2477_,
                    v___x_2478_,
                    v___x_2484_,
                );
                v___x_2486_ =
                    l_Lean_Syntax_node2(v___y_2427_, v___y_2437_, v___x_2473_, v___x_2485_);
                v___x_2487_ =
                    l_Lean_Elab_Command_elabCommand(v___x_2486_, v___y_2436_, v___y_2439_);
                crate::leanh::lean_dec_ref(v___y_2436_);
                return v___x_2487_;
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_2517_, 3);
                v___x_2524_ = l_Array_append___redArg(v___y_2517_, v___y_2523_);
                crate::leanh::lean_dec_ref(v___y_2523_);
                crate::leanh::lean_inc_n(v___y_2499_, 6);
                crate::leanh::lean_inc_n(v___y_2515_, 18);
                v___x_2525_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2525_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2525_, 1, v___y_2499_);
                crate::leanh::lean_ctor_set(v___x_2525_, 2, v___x_2524_);
                v___x_2526_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15;
                crate::leanh::lean_inc_ref(v___y_2510_);
                crate::leanh::lean_inc_ref_n(v___y_2518_, 6);
                crate::leanh::lean_inc_ref_n(v___y_2506_, 7);
                v___x_2527_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2510_, v___x_2526_);
                v___x_2528_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16;
                v___x_2529_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2529_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2529_, 1, v___x_2528_);
                crate::leanh::lean_inc_ref(v___y_2519_);
                v___x_2530_ = l_Lean_Syntax_SepArray_ofElems(v___y_2519_, v___y_2513_);
                crate::leanh::lean_dec_ref(v___y_2513_);
                v___x_2531_ = l_Array_append___redArg(v___y_2517_, v___x_2530_);
                crate::leanh::lean_dec_ref(v___x_2530_);
                v___x_2532_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2532_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2532_, 1, v___y_2499_);
                crate::leanh::lean_ctor_set(v___x_2532_, 2, v___x_2531_);
                v___x_2533_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17;
                v___x_2534_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2534_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2534_, 1, v___x_2533_);
                crate::leanh::lean_inc(v___x_2527_);
                v___x_2535_ = l_Lean_Syntax_node3(
                    v___y_2515_,
                    v___x_2527_,
                    v___x_2529_,
                    v___x_2532_,
                    v___x_2534_,
                );
                v___x_2536_ = l_Lean_Syntax_node1(v___y_2515_, v___y_2499_, v___x_2535_);
                v___x_2537_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2537_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2537_, 1, v___y_2499_);
                crate::leanh::lean_ctor_set(v___x_2537_, 2, v___y_2517_);
                crate::leanh::lean_inc_ref_n(v___x_2537_, 8);
                crate::leanh::lean_inc(v___y_2516_);
                v___x_2538_ = l_Lean_Syntax_node7(
                    v___y_2515_,
                    v___y_2516_,
                    v___x_2525_,
                    v___x_2536_,
                    v___x_2537_,
                    v___x_2537_,
                    v___x_2537_,
                    v___x_2537_,
                    v___x_2537_,
                );
                v___x_2539_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18;
                crate::leanh::lean_inc_ref_n(v___y_2501_, 3);
                v___x_2540_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2539_);
                v___x_2541_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2541_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2541_, 1, v___x_2539_);
                v___x_2542_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7;
                v___x_2543_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2542_);
                v___x_2544_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8;
                crate::leanh::lean_inc_n(v___y_2511_, 2);
                v___x_2545_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2545_, 0, v___y_2511_);
                crate::leanh::lean_ctor_set(v___x_2545_, 1, v___y_2499_);
                crate::leanh::lean_ctor_set(v___x_2545_, 2, v___x_2544_);
                v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2496_);
                crate::leanh::lean_inc(v___y_2505_);
                crate::leanh::lean_inc_ref(v___x_2546_);
                v___x_2547_ = lean_array_push(v___x_2546_, v___y_2505_);
                crate::leanh::lean_inc_ref(v___x_2545_);
                v___x_2548_ = lean_array_push(v___x_2547_, v___x_2545_);
                crate::leanh::lean_inc(v___x_2543_);
                v___x_2549_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2549_, 0, v___y_2511_);
                crate::leanh::lean_ctor_set(v___x_2549_, 1, v___x_2543_);
                crate::leanh::lean_ctor_set(v___x_2549_, 2, v___x_2548_);
                v___x_2550_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9;
                v___x_2551_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2550_);
                v___x_2552_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11;
                v___x_2553_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2510_, v___x_2552_);
                v___x_2554_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12;
                v___x_2555_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2555_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2555_, 1, v___x_2554_);
                v___x_2556_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20);
                v___x_2557_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21;
                v___x_2558_ = l_Lean_addMacroScope(v___y_2504_, v___x_2557_, v___y_2498_);
                v___x_2559_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23;
                v___x_2560_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24;
                crate::leanh::lean_inc(v___y_2502_);
                v___x_2561_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2561_, 0, v___x_2560_);
                crate::leanh::lean_ctor_set(v___x_2561_, 1, v___y_2502_);
                v___x_2562_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2562_, 0, v___x_2559_);
                crate::leanh::lean_ctor_set(v___x_2562_, 1, v___x_2561_);
                v___x_2563_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2563_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2563_, 1, v___x_2556_);
                crate::leanh::lean_ctor_set(v___x_2563_, 2, v___x_2558_);
                crate::leanh::lean_ctor_set(v___x_2563_, 3, v___x_2562_);
                v___x_2564_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___x_2553_, v___x_2555_, v___x_2563_);
                v___x_2565_ = l_Lean_Syntax_node1(v___y_2515_, v___y_2499_, v___x_2564_);
                crate::leanh::lean_inc(v___x_2551_);
                v___x_2566_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___x_2551_, v___x_2537_, v___x_2565_);
                v___x_2567_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25;
                v___x_2568_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2567_);
                crate::leanh::lean_inc_ref(v___y_2507_);
                v___x_2569_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2569_, 0, v___y_2515_);
                crate::leanh::lean_ctor_set(v___x_2569_, 1, v___y_2507_);
                v___x_2570_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26;
                v___x_2571_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27;
                v___x_2572_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___x_2570_, v___x_2571_);
                crate::leanh::lean_inc(v___x_2572_);
                v___x_2573_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___x_2572_, v___x_2537_, v___x_2537_);
                crate::leanh::lean_inc(v___x_2568_);
                v___x_2574_ = l_Lean_Syntax_node4(
                    v___y_2515_,
                    v___x_2568_,
                    v___x_2569_,
                    v___y_2509_,
                    v___x_2573_,
                    v___x_2537_,
                );
                crate::leanh::lean_inc(v___x_2540_);
                v___x_2575_ = l_Lean_Syntax_node4(
                    v___y_2515_,
                    v___x_2540_,
                    v___x_2541_,
                    v___x_2549_,
                    v___x_2566_,
                    v___x_2574_,
                );
                crate::leanh::lean_inc(v___y_2508_);
                v___x_2576_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___y_2508_, v___x_2538_, v___x_2575_);
                crate::leanh::lean_inc(v___x_2576_);
                v___x_2577_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_2577_, 0, v___x_2576_);
                v___x_2578_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                    v_stx_2416_,
                    v___x_2576_,
                    v___x_2577_,
                    v___y_2520_,
                    v___y_2521_,
                );
                if crate::leanh::lean_obj_tag(v___x_2578_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2578_, 1);
                    v___x_2579_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                            v___y_2520_,
                            v___y_2521_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2579_) == 0 {
                        v_a_2580_ = crate::leanh::lean_ctor_get(v___x_2579_, 0);
                        crate::leanh::lean_inc(v_a_2580_);
                        crate::leanh::lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2581_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2520_);
                        if crate::leanh::lean_obj_tag(v___x_2581_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2581_, 1);
                            v___x_2582_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28;
                            v___x_2583_ = l_Lean_Name_str___override(v___y_2503_, v___x_2582_);
                            v___x_2584_ = l_Lean_mkIdentFrom(v___y_2505_, v___x_2583_, v___y_2500_);
                            crate::leanh::lean_dec(v___y_2505_);
                            if crate::leanh::lean_obj_tag(v___y_2512_) == 0 {
                                v___x_2585_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2521_);
                                crate::leanh::lean_dec_ref(v___x_2585_);
                                v___y_2421_ = v___y_2499_;
                                v___y_2422_ = v___x_2546_;
                                v___y_2423_ = v___y_2511_;
                                v___y_2424_ = v___x_2533_;
                                v___y_2425_ = v___y_2514_;
                                v___y_2426_ = v___x_2568_;
                                v___y_2427_ = v_a_2580_;
                                v___y_2428_ = v___x_2572_;
                                v___y_2429_ = v___y_2516_;
                                v___y_2430_ = v___x_2584_;
                                v___y_2431_ = v___x_2545_;
                                v___y_2432_ = v___y_2517_;
                                v___y_2433_ = v___y_2506_;
                                v___y_2434_ = v___x_2527_;
                                v___y_2435_ = v___y_2507_;
                                v___y_2436_ = v___y_2520_;
                                v___y_2437_ = v___y_2508_;
                                v___y_2438_ = v___x_2539_;
                                v___y_2439_ = v___y_2521_;
                                v___y_2440_ = v___x_2540_;
                                v___y_2441_ = v___y_2522_;
                                v___y_2442_ = v___x_2551_;
                                v___y_2443_ = v___x_2543_;
                                v___y_2444_ = v___x_2528_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref_known(v___y_2512_, 1);
                                v___y_2421_ = v___y_2499_;
                                v___y_2422_ = v___x_2546_;
                                v___y_2423_ = v___y_2511_;
                                v___y_2424_ = v___x_2533_;
                                v___y_2425_ = v___y_2514_;
                                v___y_2426_ = v___x_2568_;
                                v___y_2427_ = v_a_2580_;
                                v___y_2428_ = v___x_2572_;
                                v___y_2429_ = v___y_2516_;
                                v___y_2430_ = v___x_2584_;
                                v___y_2431_ = v___x_2545_;
                                v___y_2432_ = v___y_2517_;
                                v___y_2433_ = v___y_2506_;
                                v___y_2434_ = v___x_2527_;
                                v___y_2435_ = v___y_2507_;
                                v___y_2436_ = v___y_2520_;
                                v___y_2437_ = v___y_2508_;
                                v___y_2438_ = v___x_2539_;
                                v___y_2439_ = v___y_2521_;
                                v___y_2440_ = v___x_2540_;
                                v___y_2441_ = v___y_2522_;
                                v___y_2442_ = v___x_2551_;
                                v___y_2443_ = v___x_2543_;
                                v___y_2444_ = v___x_2528_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2580_);
                            crate::leanh::lean_dec(v___x_2572_);
                            crate::leanh::lean_dec(v___x_2568_);
                            crate::leanh::lean_dec(v___x_2551_);
                            crate::leanh::lean_dec_ref(v___x_2546_);
                            crate::leanh::lean_dec_ref_known(v___x_2545_, 3);
                            crate::leanh::lean_dec(v___x_2543_);
                            crate::leanh::lean_dec(v___x_2540_);
                            crate::leanh::lean_dec(v___x_2527_);
                            crate::leanh::lean_dec(v___y_2522_);
                            crate::leanh::lean_dec_ref(v___y_2520_);
                            crate::leanh::lean_dec(v___y_2516_);
                            crate::leanh::lean_dec(v___y_2514_);
                            crate::leanh::lean_dec(v___y_2512_);
                            crate::leanh::lean_dec(v___y_2511_);
                            crate::leanh::lean_dec(v___y_2508_);
                            crate::leanh::lean_dec(v___y_2505_);
                            crate::leanh::lean_dec(v___y_2503_);
                            v_a_2586_ = crate::leanh::lean_ctor_get(v___x_2581_, 0);
                            v_isSharedCheck_2593_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2581_)) as u8;
                            if v_isSharedCheck_2593_ == 0 {
                                v___x_2588_ = v___x_2581_;
                                v_isShared_2589_ = v_isSharedCheck_2593_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2586_);
                                crate::leanh::lean_dec(v___x_2581_);
                                v___x_2588_ = crate::leanh::lean_box(0);
                                v_isShared_2589_ = v_isSharedCheck_2593_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2572_);
                        crate::leanh::lean_dec(v___x_2568_);
                        crate::leanh::lean_dec(v___x_2551_);
                        crate::leanh::lean_dec_ref(v___x_2546_);
                        crate::leanh::lean_dec_ref_known(v___x_2545_, 3);
                        crate::leanh::lean_dec(v___x_2543_);
                        crate::leanh::lean_dec(v___x_2540_);
                        crate::leanh::lean_dec(v___x_2527_);
                        crate::leanh::lean_dec(v___y_2522_);
                        crate::leanh::lean_dec_ref(v___y_2520_);
                        crate::leanh::lean_dec(v___y_2516_);
                        crate::leanh::lean_dec(v___y_2514_);
                        crate::leanh::lean_dec(v___y_2512_);
                        crate::leanh::lean_dec(v___y_2511_);
                        crate::leanh::lean_dec(v___y_2508_);
                        crate::leanh::lean_dec(v___y_2505_);
                        crate::leanh::lean_dec(v___y_2503_);
                        v_a_2594_ = crate::leanh::lean_ctor_get(v___x_2579_, 0);
                        v_isSharedCheck_2601_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2579_)) as u8;
                        if v_isSharedCheck_2601_ == 0 {
                            v___x_2596_ = v___x_2579_;
                            v_isShared_2597_ = v_isSharedCheck_2601_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2594_);
                            crate::leanh::lean_dec(v___x_2579_);
                            v___x_2596_ = crate::leanh::lean_box(0);
                            v_isShared_2597_ = v_isSharedCheck_2601_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2572_);
                    crate::leanh::lean_dec(v___x_2568_);
                    crate::leanh::lean_dec(v___x_2551_);
                    crate::leanh::lean_dec_ref(v___x_2546_);
                    crate::leanh::lean_dec_ref_known(v___x_2545_, 3);
                    crate::leanh::lean_dec(v___x_2543_);
                    crate::leanh::lean_dec(v___x_2540_);
                    crate::leanh::lean_dec(v___x_2527_);
                    crate::leanh::lean_dec(v___y_2522_);
                    crate::leanh::lean_dec_ref(v___y_2520_);
                    crate::leanh::lean_dec(v___y_2516_);
                    crate::leanh::lean_dec(v___y_2514_);
                    crate::leanh::lean_dec(v___y_2512_);
                    crate::leanh::lean_dec(v___y_2511_);
                    crate::leanh::lean_dec(v___y_2508_);
                    crate::leanh::lean_dec(v___y_2505_);
                    crate::leanh::lean_dec(v___y_2503_);
                    return v___x_2578_;
                }
            }
            3 => {
                if v_isShared_2589_ == 0 {
                    v___x_2591_ = v___x_2588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
                    v___x_2591_ = v_reuseFailAlloc_2592_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2591_;
            }
            5 => {
                if v_isShared_2597_ == 0 {
                    v___x_2599_ = v___x_2596_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
                    v___x_2599_ = v_reuseFailAlloc_2600_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2599_;
            }
            7 => {
                v___x_2626_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                v___x_2627_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_2618_, 2);
                crate::leanh::lean_inc_ref_n(v___y_2617_, 2);
                v___x_2628_ =
                    l_Lean_Name_mkStr4(v___y_2617_, v___y_2618_, v___x_2626_, v___x_2627_);
                v___x_2629_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1;
                v___x_2630_ =
                    l_Lean_Name_mkStr4(v___y_2617_, v___y_2618_, v___x_2626_, v___x_2629_);
                if crate::leanh::lean_obj_tag(v___y_2622_) == 1 {
                    v_val_2631_ = crate::leanh::lean_ctor_get(v___y_2622_, 0);
                    crate::leanh::lean_inc(v_val_2631_);
                    crate::leanh::lean_dec_ref_known(v___y_2622_, 1);
                    v___x_2632_ = l_Array_mkArray1___redArg(v_val_2631_);
                    v___y_2498_ = v___y_2603_;
                    v___y_2499_ = v___y_2604_;
                    v___y_2500_ = v___y_2607_;
                    v___y_2501_ = v___x_2626_;
                    v___y_2502_ = v___y_2613_;
                    v___y_2503_ = v___y_2614_;
                    v___y_2504_ = v_a_2625_;
                    v___y_2505_ = v___y_2615_;
                    v___y_2506_ = v___y_2617_;
                    v___y_2507_ = v___y_2619_;
                    v___y_2508_ = v___x_2628_;
                    v___y_2509_ = v___y_2605_;
                    v___y_2510_ = v___y_2606_;
                    v___y_2511_ = v___y_2608_;
                    v___y_2512_ = v___y_2611_;
                    v___y_2513_ = v___y_2610_;
                    v___y_2514_ = v___y_2609_;
                    v___y_2515_ = v___y_2612_;
                    v___y_2516_ = v___x_2630_;
                    v___y_2517_ = v___y_2616_;
                    v___y_2518_ = v___y_2618_;
                    v___y_2519_ = v___y_2621_;
                    v___y_2520_ = v___y_2620_;
                    v___y_2521_ = v___y_2623_;
                    v___y_2522_ = v___y_2624_;
                    v___y_2523_ = v___x_2632_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2622_);
                    v___x_2633_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                    v___y_2498_ = v___y_2603_;
                    v___y_2499_ = v___y_2604_;
                    v___y_2500_ = v___y_2607_;
                    v___y_2501_ = v___x_2626_;
                    v___y_2502_ = v___y_2613_;
                    v___y_2503_ = v___y_2614_;
                    v___y_2504_ = v_a_2625_;
                    v___y_2505_ = v___y_2615_;
                    v___y_2506_ = v___y_2617_;
                    v___y_2507_ = v___y_2619_;
                    v___y_2508_ = v___x_2628_;
                    v___y_2509_ = v___y_2605_;
                    v___y_2510_ = v___y_2606_;
                    v___y_2511_ = v___y_2608_;
                    v___y_2512_ = v___y_2611_;
                    v___y_2513_ = v___y_2610_;
                    v___y_2514_ = v___y_2609_;
                    v___y_2515_ = v___y_2612_;
                    v___y_2516_ = v___x_2630_;
                    v___y_2517_ = v___y_2616_;
                    v___y_2518_ = v___y_2618_;
                    v___y_2519_ = v___y_2621_;
                    v___y_2520_ = v___y_2620_;
                    v___y_2521_ = v___y_2623_;
                    v___y_2522_ = v___y_2624_;
                    v___y_2523_ = v___x_2633_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_2659_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30;
                crate::leanh::lean_inc_ref_n(v___y_2636_, 6);
                crate::leanh::lean_inc_ref_n(v___y_2651_, 6);
                crate::leanh::lean_inc_ref_n(v___y_2650_, 6);
                v___x_2660_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2659_);
                v___x_2661_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31;
                crate::leanh::lean_inc_n(v___y_2640_, 28);
                v___x_2662_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2662_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2662_, 1, v___x_2661_);
                crate::leanh::lean_inc_ref(v___y_2648_);
                crate::leanh::lean_inc_n(v___y_2635_, 6);
                v___x_2663_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2663_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2663_, 1, v___y_2635_);
                crate::leanh::lean_ctor_set(v___x_2663_, 2, v___y_2648_);
                v___x_2664_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31;
                v___x_2665_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2664_);
                v___x_2666_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32;
                v___x_2667_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2666_);
                v___x_2668_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33;
                v___x_2669_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2668_);
                v___x_2670_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35);
                v___x_2671_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36;
                crate::leanh::lean_inc_n(v___y_2652_, 3);
                crate::leanh::lean_inc_n(v_a_2658_, 3);
                v___x_2672_ = l_Lean_addMacroScope(v_a_2658_, v___x_2671_, v___y_2652_);
                crate::leanh::lean_inc_n(v___y_2646_, 4);
                v___x_2673_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2673_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2673_, 1, v___x_2670_);
                crate::leanh::lean_ctor_set(v___x_2673_, 2, v___x_2672_);
                crate::leanh::lean_ctor_set(v___x_2673_, 3, v___y_2646_);
                crate::leanh::lean_inc_ref_n(v___x_2663_, 18);
                crate::leanh::lean_inc_n(v___x_2669_, 3);
                v___x_2674_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2669_, v___x_2673_, v___x_2663_);
                v___x_2675_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37;
                v___x_2676_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2675_);
                v___x_2677_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38;
                v___x_2678_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2678_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2678_, 1, v___x_2677_);
                crate::leanh::lean_inc_ref_n(v___x_2678_, 3);
                crate::leanh::lean_inc_n(v___x_2676_, 3);
                v___x_2679_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___x_2676_,
                    v___x_2678_,
                    v___x_2663_,
                    v___y_2639_,
                );
                v___x_2680_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___y_2635_,
                    v___x_2663_,
                    v___x_2663_,
                    v___x_2679_,
                );
                crate::leanh::lean_inc_n(v___x_2667_, 3);
                v___x_2681_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2667_, v___x_2674_, v___x_2680_);
                v___x_2682_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39;
                v___x_2683_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2683_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2683_, 1, v___x_2682_);
                v___x_2684_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41);
                v___x_2685_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42;
                v___x_2686_ = l_Lean_addMacroScope(v_a_2658_, v___x_2685_, v___y_2652_);
                v___x_2687_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2687_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2687_, 1, v___x_2684_);
                crate::leanh::lean_ctor_set(v___x_2687_, 2, v___x_2686_);
                crate::leanh::lean_ctor_set(v___x_2687_, 3, v___y_2646_);
                v___x_2688_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2669_, v___x_2687_, v___x_2663_);
                v___x_2689_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___x_2676_,
                    v___x_2678_,
                    v___x_2663_,
                    v___y_2637_,
                );
                v___x_2690_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___y_2635_,
                    v___x_2663_,
                    v___x_2663_,
                    v___x_2689_,
                );
                v___x_2691_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2667_, v___x_2688_, v___x_2690_);
                v___x_2692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44);
                v___x_2693_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45;
                v___x_2694_ = l_Lean_addMacroScope(v_a_2658_, v___x_2693_, v___y_2652_);
                v___x_2695_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2695_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2695_, 1, v___x_2692_);
                crate::leanh::lean_ctor_set(v___x_2695_, 2, v___x_2694_);
                crate::leanh::lean_ctor_set(v___x_2695_, 3, v___y_2646_);
                v___x_2696_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2669_, v___x_2695_, v___x_2663_);
                v___x_2697_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___x_2676_,
                    v___x_2678_,
                    v___x_2663_,
                    v___y_2655_,
                );
                v___x_2698_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___y_2635_,
                    v___x_2663_,
                    v___x_2663_,
                    v___x_2697_,
                );
                v___x_2699_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2667_, v___x_2696_, v___x_2698_);
                v___x_2700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47);
                v___x_2701_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48;
                v___x_2702_ = l_Lean_addMacroScope(v_a_2658_, v___x_2701_, v___y_2652_);
                v___x_2703_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2703_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2703_, 1, v___x_2700_);
                crate::leanh::lean_ctor_set(v___x_2703_, 2, v___x_2702_);
                crate::leanh::lean_ctor_set(v___x_2703_, 3, v___y_2646_);
                v___x_2704_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2669_, v___x_2703_, v___x_2663_);
                v___x_2705_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___x_2676_,
                    v___x_2678_,
                    v___x_2663_,
                    v___y_2649_,
                );
                v___x_2706_ = l_Lean_Syntax_node3(
                    v___y_2640_,
                    v___y_2635_,
                    v___x_2663_,
                    v___x_2663_,
                    v___x_2705_,
                );
                v___x_2707_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2667_, v___x_2704_, v___x_2706_);
                crate::leanh::lean_inc_ref_n(v___x_2683_, 2);
                v___x_2708_ = l_Lean_Syntax_node7(
                    v___y_2640_,
                    v___y_2635_,
                    v___x_2681_,
                    v___x_2683_,
                    v___x_2691_,
                    v___x_2683_,
                    v___x_2699_,
                    v___x_2683_,
                    v___x_2707_,
                );
                v___x_2709_ = l_Lean_Syntax_node1(v___y_2640_, v___x_2665_, v___x_2708_);
                v___x_2710_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49;
                v___x_2711_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2710_);
                v___x_2712_ = l_Lean_Syntax_node1(v___y_2640_, v___x_2711_, v___x_2663_);
                v___x_2713_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50;
                v___x_2714_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2714_, 0, v___y_2640_);
                crate::leanh::lean_ctor_set(v___x_2714_, 1, v___x_2713_);
                v___x_2715_ = l_Lean_Syntax_node6(
                    v___y_2640_,
                    v___x_2660_,
                    v___x_2662_,
                    v___x_2663_,
                    v___x_2709_,
                    v___x_2712_,
                    v___x_2663_,
                    v___x_2714_,
                );
                v___x_2716_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                    v___y_2653_,
                    v___y_2656_,
                );
                if crate::leanh::lean_obj_tag(v___x_2716_) == 0 {
                    v_a_2717_ = crate::leanh::lean_ctor_get(v___x_2716_, 0);
                    crate::leanh::lean_inc(v_a_2717_);
                    crate::leanh::lean_dec_ref_known(v___x_2716_, 1);
                    v___x_2718_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2653_);
                    if crate::leanh::lean_obj_tag(v___x_2718_) == 0 {
                        if crate::leanh::lean_obj_tag(v___y_2642_) == 0 {
                            v_a_2719_ = crate::leanh::lean_ctor_get(v___x_2718_, 0);
                            crate::leanh::lean_inc(v_a_2719_);
                            crate::leanh::lean_dec_ref_known(v___x_2718_, 1);
                            v___x_2720_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2656_);
                            v_a_2721_ = crate::leanh::lean_ctor_get(v___x_2720_, 0);
                            crate::leanh::lean_inc(v_a_2721_);
                            crate::leanh::lean_dec_ref(v___x_2720_);
                            v___y_2603_ = v_a_2719_;
                            v___y_2604_ = v___y_2635_;
                            v___y_2605_ = v___x_2715_;
                            v___y_2606_ = v___y_2636_;
                            v___y_2607_ = v___y_2638_;
                            v___y_2608_ = v___y_2641_;
                            v___y_2609_ = v___y_2644_;
                            v___y_2610_ = v___y_2643_;
                            v___y_2611_ = v___y_2642_;
                            v___y_2612_ = v_a_2717_;
                            v___y_2613_ = v___y_2646_;
                            v___y_2614_ = v___y_2645_;
                            v___y_2615_ = v___y_2647_;
                            v___y_2616_ = v___y_2648_;
                            v___y_2617_ = v___y_2650_;
                            v___y_2618_ = v___y_2651_;
                            v___y_2619_ = v___x_2677_;
                            v___y_2620_ = v___y_2653_;
                            v___y_2621_ = v___x_2682_;
                            v___y_2622_ = v___y_2654_;
                            v___y_2623_ = v___y_2656_;
                            v___y_2624_ = v___y_2657_;
                            v_a_2625_ = v_a_2721_;
                            state = 7;
                            continue;
                        } else {
                            v_a_2722_ = crate::leanh::lean_ctor_get(v___x_2718_, 0);
                            crate::leanh::lean_inc(v_a_2722_);
                            crate::leanh::lean_dec_ref_known(v___x_2718_, 1);
                            v_val_2723_ = crate::leanh::lean_ctor_get(v___y_2642_, 0);
                            crate::leanh::lean_inc(v_val_2723_);
                            v___y_2603_ = v_a_2722_;
                            v___y_2604_ = v___y_2635_;
                            v___y_2605_ = v___x_2715_;
                            v___y_2606_ = v___y_2636_;
                            v___y_2607_ = v___y_2638_;
                            v___y_2608_ = v___y_2641_;
                            v___y_2609_ = v___y_2644_;
                            v___y_2610_ = v___y_2643_;
                            v___y_2611_ = v___y_2642_;
                            v___y_2612_ = v_a_2717_;
                            v___y_2613_ = v___y_2646_;
                            v___y_2614_ = v___y_2645_;
                            v___y_2615_ = v___y_2647_;
                            v___y_2616_ = v___y_2648_;
                            v___y_2617_ = v___y_2650_;
                            v___y_2618_ = v___y_2651_;
                            v___y_2619_ = v___x_2677_;
                            v___y_2620_ = v___y_2653_;
                            v___y_2621_ = v___x_2682_;
                            v___y_2622_ = v___y_2654_;
                            v___y_2623_ = v___y_2656_;
                            v___y_2624_ = v___y_2657_;
                            v_a_2625_ = v_val_2723_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2717_);
                        crate::leanh::lean_dec(v___x_2715_);
                        crate::leanh::lean_dec(v___y_2657_);
                        crate::leanh::lean_dec(v___y_2654_);
                        crate::leanh::lean_dec_ref(v___y_2653_);
                        crate::leanh::lean_dec_ref(v___y_2651_);
                        crate::leanh::lean_dec(v___y_2647_);
                        crate::leanh::lean_dec(v___y_2645_);
                        crate::leanh::lean_dec(v___y_2644_);
                        crate::leanh::lean_dec_ref(v___y_2643_);
                        crate::leanh::lean_dec(v___y_2642_);
                        crate::leanh::lean_dec(v___y_2641_);
                        crate::leanh::lean_dec_ref(v___y_2636_);
                        crate::leanh::lean_dec(v_stx_2416_);
                        v_a_2724_ = crate::leanh::lean_ctor_get(v___x_2718_, 0);
                        v_isSharedCheck_2731_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2718_)) as u8;
                        if v_isSharedCheck_2731_ == 0 {
                            v___x_2726_ = v___x_2718_;
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2724_);
                            crate::leanh::lean_dec(v___x_2718_);
                            v___x_2726_ = crate::leanh::lean_box(0);
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2715_);
                    crate::leanh::lean_dec(v___y_2657_);
                    crate::leanh::lean_dec(v___y_2654_);
                    crate::leanh::lean_dec_ref(v___y_2653_);
                    crate::leanh::lean_dec_ref(v___y_2651_);
                    crate::leanh::lean_dec(v___y_2647_);
                    crate::leanh::lean_dec(v___y_2645_);
                    crate::leanh::lean_dec(v___y_2644_);
                    crate::leanh::lean_dec_ref(v___y_2643_);
                    crate::leanh::lean_dec(v___y_2642_);
                    crate::leanh::lean_dec(v___y_2641_);
                    crate::leanh::lean_dec_ref(v___y_2636_);
                    crate::leanh::lean_dec(v_stx_2416_);
                    v_a_2732_ = crate::leanh::lean_ctor_get(v___x_2716_, 0);
                    v_isSharedCheck_2739_ = (!crate::leanh::lean_is_exclusive(v___x_2716_)) as u8;
                    if v_isSharedCheck_2739_ == 0 {
                        v___x_2734_ = v___x_2716_;
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2732_);
                        crate::leanh::lean_dec(v___x_2716_);
                        v___x_2734_ = crate::leanh::lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_2727_ == 0 {
                    v___x_2729_ = v___x_2726_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2730_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
                    v___x_2729_ = v_reuseFailAlloc_2730_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2729_;
            }
            11 => {
                if v_isShared_2735_ == 0 {
                    v___x_2737_ = v___x_2734_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
                    v___x_2737_ = v_reuseFailAlloc_2738_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2737_;
            }
            13 => {
                v___x_2758_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15;
                v___x_2759_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10;
                v___x_2760_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51;
                crate::leanh::lean_inc_ref_n(v___y_2750_, 2);
                v___x_2761_ =
                    l_Lean_Name_mkStr4(v___y_2750_, v___x_2758_, v___x_2759_, v___x_2760_);
                v___x_2762_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52;
                v___x_2763_ =
                    l_Lean_Name_mkStr4(v___y_2750_, v___x_2758_, v___x_2759_, v___x_2762_);
                v___x_2764_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                v___x_2765_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                crate::leanh::lean_inc_n(v___y_2756_, 2);
                v___x_2766_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2766_, 0, v___y_2756_);
                crate::leanh::lean_ctor_set(v___x_2766_, 1, v___x_2764_);
                crate::leanh::lean_ctor_set(v___x_2766_, 2, v___x_2765_);
                crate::leanh::lean_inc_ref(v___x_2766_);
                crate::leanh::lean_inc(v___x_2763_);
                v___x_2767_ = l_Lean_Syntax_node1(v___y_2756_, v___x_2763_, v___x_2766_);
                v___x_2768_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                    v___y_2751_,
                    v___y_2755_,
                );
                if crate::leanh::lean_obj_tag(v___x_2768_) == 0 {
                    v_a_2769_ = crate::leanh::lean_ctor_get(v___x_2768_, 0);
                    crate::leanh::lean_inc(v_a_2769_);
                    crate::leanh::lean_dec_ref_known(v___x_2768_, 1);
                    v___x_2770_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2751_);
                    if crate::leanh::lean_obj_tag(v___x_2770_) == 0 {
                        v_a_2771_ = crate::leanh::lean_ctor_get(v___x_2770_, 0);
                        crate::leanh::lean_inc(v_a_2771_);
                        crate::leanh::lean_dec_ref_known(v___x_2770_, 1);
                        v___x_2772_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54);
                        v___x_2773_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56;
                        v___x_2774_ = l_Lean_addMacroScope(v_a_2757_, v___x_2773_, v___y_2747_);
                        crate::leanh::lean_inc(v___y_2748_);
                        crate::leanh::lean_inc_n(v___y_2756_, 2);
                        v___x_2775_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2775_, 0, v___y_2756_);
                        crate::leanh::lean_ctor_set(v___x_2775_, 1, v___x_2772_);
                        crate::leanh::lean_ctor_set(v___x_2775_, 2, v___x_2774_);
                        crate::leanh::lean_ctor_set(v___x_2775_, 3, v___y_2748_);
                        v___x_2776_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57;
                        v___x_2777_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58;
                        crate::leanh::lean_inc_ref(v___y_2750_);
                        v___x_2778_ =
                            l_Lean_Name_mkStr4(v___y_2750_, v___x_2758_, v___x_2776_, v___x_2777_);
                        v___x_2779_ =
                            l_Lean_Syntax_node2(v___y_2756_, v___x_2778_, v___x_2775_, v___x_2766_);
                        crate::leanh::lean_inc(v___x_2761_);
                        v___x_2780_ =
                            l_Lean_Syntax_node2(v___y_2756_, v___x_2761_, v___x_2767_, v___x_2779_);
                        v___x_2781_ = lean_mk_empty_array_with_capacity(v___x_2494_);
                        v___x_2782_ = lean_array_push(v___x_2781_, v___x_2780_);
                        v___x_2783_ = l_Lake_DSL_expandAttrs(v___y_2754_);
                        v___x_2784_ = l_Array_append___redArg(v___x_2782_, v___x_2783_);
                        crate::leanh::lean_dec_ref(v___x_2783_);
                        v___x_2785_ = l_Lake_DSL_packageDeclName;
                        v___x_2786_ = l_Lean_mkIdentFrom(v___y_2745_, v___x_2785_, v___y_2742_);
                        crate::leanh::lean_dec(v___y_2745_);
                        if crate::leanh::lean_obj_tag(v___y_2746_) == 0 {
                            v___x_2787_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2755_);
                            v_a_2788_ = crate::leanh::lean_ctor_get(v___x_2787_, 0);
                            crate::leanh::lean_inc(v_a_2788_);
                            crate::leanh::lean_dec_ref(v___x_2787_);
                            v___y_2635_ = v___x_2764_;
                            v___y_2636_ = v___x_2759_;
                            v___y_2637_ = v___y_2741_;
                            v___y_2638_ = v___y_2742_;
                            v___y_2639_ = v___y_2743_;
                            v___y_2640_ = v_a_2769_;
                            v___y_2641_ = v___y_2744_;
                            v___y_2642_ = v___y_2746_;
                            v___y_2643_ = v___x_2784_;
                            v___y_2644_ = v___x_2763_;
                            v___y_2645_ = v___x_2785_;
                            v___y_2646_ = v___y_2748_;
                            v___y_2647_ = v___x_2786_;
                            v___y_2648_ = v___x_2765_;
                            v___y_2649_ = v___y_2749_;
                            v___y_2650_ = v___y_2750_;
                            v___y_2651_ = v___x_2758_;
                            v___y_2652_ = v_a_2771_;
                            v___y_2653_ = v___y_2751_;
                            v___y_2654_ = v___y_2752_;
                            v___y_2655_ = v___y_2753_;
                            v___y_2656_ = v___y_2755_;
                            v___y_2657_ = v___x_2761_;
                            v_a_2658_ = v_a_2788_;
                            state = 8;
                            continue;
                        } else {
                            v_val_2789_ = crate::leanh::lean_ctor_get(v___y_2746_, 0);
                            crate::leanh::lean_inc(v_val_2789_);
                            v___y_2635_ = v___x_2764_;
                            v___y_2636_ = v___x_2759_;
                            v___y_2637_ = v___y_2741_;
                            v___y_2638_ = v___y_2742_;
                            v___y_2639_ = v___y_2743_;
                            v___y_2640_ = v_a_2769_;
                            v___y_2641_ = v___y_2744_;
                            v___y_2642_ = v___y_2746_;
                            v___y_2643_ = v___x_2784_;
                            v___y_2644_ = v___x_2763_;
                            v___y_2645_ = v___x_2785_;
                            v___y_2646_ = v___y_2748_;
                            v___y_2647_ = v___x_2786_;
                            v___y_2648_ = v___x_2765_;
                            v___y_2649_ = v___y_2749_;
                            v___y_2650_ = v___y_2750_;
                            v___y_2651_ = v___x_2758_;
                            v___y_2652_ = v_a_2771_;
                            v___y_2653_ = v___y_2751_;
                            v___y_2654_ = v___y_2752_;
                            v___y_2655_ = v___y_2753_;
                            v___y_2656_ = v___y_2755_;
                            v___y_2657_ = v___x_2761_;
                            v_a_2658_ = v_val_2789_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2769_);
                        crate::leanh::lean_dec(v___x_2767_);
                        crate::leanh::lean_dec_ref_known(v___x_2766_, 3);
                        crate::leanh::lean_dec(v___x_2763_);
                        crate::leanh::lean_dec(v___x_2761_);
                        crate::leanh::lean_dec(v_a_2757_);
                        crate::leanh::lean_dec(v___y_2756_);
                        crate::leanh::lean_dec(v___y_2754_);
                        crate::leanh::lean_dec(v___y_2753_);
                        crate::leanh::lean_dec(v___y_2752_);
                        crate::leanh::lean_dec_ref(v___y_2751_);
                        crate::leanh::lean_dec(v___y_2749_);
                        crate::leanh::lean_dec(v___y_2747_);
                        crate::leanh::lean_dec(v___y_2746_);
                        crate::leanh::lean_dec(v___y_2745_);
                        crate::leanh::lean_dec(v___y_2744_);
                        crate::leanh::lean_dec(v___y_2743_);
                        crate::leanh::lean_dec(v___y_2741_);
                        crate::leanh::lean_dec(v_stx_2416_);
                        v_a_2790_ = crate::leanh::lean_ctor_get(v___x_2770_, 0);
                        v_isSharedCheck_2797_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2770_)) as u8;
                        if v_isSharedCheck_2797_ == 0 {
                            v___x_2792_ = v___x_2770_;
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2790_);
                            crate::leanh::lean_dec(v___x_2770_);
                            v___x_2792_ = crate::leanh::lean_box(0);
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2767_);
                    crate::leanh::lean_dec_ref_known(v___x_2766_, 3);
                    crate::leanh::lean_dec(v___x_2763_);
                    crate::leanh::lean_dec(v___x_2761_);
                    crate::leanh::lean_dec(v_a_2757_);
                    crate::leanh::lean_dec(v___y_2756_);
                    crate::leanh::lean_dec(v___y_2754_);
                    crate::leanh::lean_dec(v___y_2753_);
                    crate::leanh::lean_dec(v___y_2752_);
                    crate::leanh::lean_dec_ref(v___y_2751_);
                    crate::leanh::lean_dec(v___y_2749_);
                    crate::leanh::lean_dec(v___y_2747_);
                    crate::leanh::lean_dec(v___y_2746_);
                    crate::leanh::lean_dec(v___y_2745_);
                    crate::leanh::lean_dec(v___y_2744_);
                    crate::leanh::lean_dec(v___y_2743_);
                    crate::leanh::lean_dec(v___y_2741_);
                    crate::leanh::lean_dec(v_stx_2416_);
                    v_a_2798_ = crate::leanh::lean_ctor_get(v___x_2768_, 0);
                    v_isSharedCheck_2805_ = (!crate::leanh::lean_is_exclusive(v___x_2768_)) as u8;
                    if v_isSharedCheck_2805_ == 0 {
                        v___x_2800_ = v___x_2768_;
                        v_isShared_2801_ = v_isSharedCheck_2805_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2798_);
                        crate::leanh::lean_dec(v___x_2768_);
                        v___x_2800_ = crate::leanh::lean_box(0);
                        v_isShared_2801_ = v_isSharedCheck_2805_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_2793_ == 0 {
                    v___x_2795_ = v___x_2792_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2796_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
                    v___x_2795_ = v_reuseFailAlloc_2796_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2795_;
            }
            16 => {
                if v_isShared_2801_ == 0 {
                    v___x_2803_ = v___x_2800_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
                    v___x_2803_ = v_reuseFailAlloc_2804_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2803_;
            }
            18 => {
                v___x_2820_ = l_Nat_reprFast(v___y_2813_);
                v___x_2821_ = crate::leanh::lean_box(2);
                v___x_2822_ = l_Lean_Syntax_mkNumLit(v___x_2820_, v___x_2821_);
                v___x_2823_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                v___x_2824_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61;
                v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2496_);
                crate::leanh::lean_inc(v___y_2819_);
                crate::leanh::lean_inc_ref(v___x_2825_);
                v___x_2826_ = lean_array_push(v___x_2825_, v___y_2819_);
                v___x_2827_ = lean_array_push(v___x_2826_, v___x_2822_);
                v___x_2828_ = l_Lean_Syntax_mkCApp(v___x_2824_, v___x_2827_);
                v___x_2829_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63;
                crate::leanh::lean_inc(v___x_2828_);
                v___x_2830_ = lean_array_push(v___x_2825_, v___x_2828_);
                crate::leanh::lean_inc(v___y_2807_);
                v___x_2831_ = lean_array_push(v___x_2830_, v___y_2807_);
                v___x_2832_ = l_Lean_Syntax_mkCApp(v___x_2829_, v___x_2831_);
                crate::leanh::lean_inc(v___y_2812_);
                v___x_2833_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_2829_, v___y_2812_, v___x_2832_, v___y_2814_, v___y_2815_, v___y_2818_);
                if crate::leanh::lean_obj_tag(v___x_2833_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2833_, 1);
                    v___x_2834_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                            v___y_2815_,
                            v___y_2818_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_2834_) == 0 {
                        v_a_2835_ = crate::leanh::lean_ctor_get(v___x_2834_, 0);
                        crate::leanh::lean_inc(v_a_2835_);
                        crate::leanh::lean_dec_ref_known(v___x_2834_, 1);
                        v___x_2836_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2815_);
                        if crate::leanh::lean_obj_tag(v___x_2836_) == 0 {
                            if crate::leanh::lean_obj_tag(v___y_2810_) == 0 {
                                v_a_2837_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                                crate::leanh::lean_inc(v_a_2837_);
                                crate::leanh::lean_dec_ref_known(v___x_2836_, 1);
                                v___x_2838_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2818_);
                                v_a_2839_ = crate::leanh::lean_ctor_get(v___x_2838_, 0);
                                crate::leanh::lean_inc(v_a_2839_);
                                crate::leanh::lean_dec_ref(v___x_2838_);
                                v___y_2741_ = v___y_2807_;
                                v___y_2742_ = v___y_2808_;
                                v___y_2743_ = v___y_2819_;
                                v___y_2744_ = v___x_2821_;
                                v___y_2745_ = v___y_2809_;
                                v___y_2746_ = v___y_2810_;
                                v___y_2747_ = v_a_2837_;
                                v___y_2748_ = v___y_2811_;
                                v___y_2749_ = v___y_2812_;
                                v___y_2750_ = v___x_2823_;
                                v___y_2751_ = v___y_2815_;
                                v___y_2752_ = v___y_2816_;
                                v___y_2753_ = v___x_2828_;
                                v___y_2754_ = v___y_2817_;
                                v___y_2755_ = v___y_2818_;
                                v___y_2756_ = v_a_2835_;
                                v_a_2757_ = v_a_2839_;
                                state = 13;
                                continue;
                            } else {
                                v_a_2840_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                                crate::leanh::lean_inc(v_a_2840_);
                                crate::leanh::lean_dec_ref_known(v___x_2836_, 1);
                                v_val_2841_ = crate::leanh::lean_ctor_get(v___y_2810_, 0);
                                crate::leanh::lean_inc(v_val_2841_);
                                v___y_2741_ = v___y_2807_;
                                v___y_2742_ = v___y_2808_;
                                v___y_2743_ = v___y_2819_;
                                v___y_2744_ = v___x_2821_;
                                v___y_2745_ = v___y_2809_;
                                v___y_2746_ = v___y_2810_;
                                v___y_2747_ = v_a_2840_;
                                v___y_2748_ = v___y_2811_;
                                v___y_2749_ = v___y_2812_;
                                v___y_2750_ = v___x_2823_;
                                v___y_2751_ = v___y_2815_;
                                v___y_2752_ = v___y_2816_;
                                v___y_2753_ = v___x_2828_;
                                v___y_2754_ = v___y_2817_;
                                v___y_2755_ = v___y_2818_;
                                v___y_2756_ = v_a_2835_;
                                v_a_2757_ = v_val_2841_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2835_);
                            crate::leanh::lean_dec(v___x_2828_);
                            crate::leanh::lean_dec(v___y_2819_);
                            crate::leanh::lean_dec(v___y_2817_);
                            crate::leanh::lean_dec(v___y_2816_);
                            crate::leanh::lean_dec_ref(v___y_2815_);
                            crate::leanh::lean_dec(v___y_2812_);
                            crate::leanh::lean_dec(v___y_2810_);
                            crate::leanh::lean_dec(v___y_2809_);
                            crate::leanh::lean_dec(v___y_2807_);
                            crate::leanh::lean_dec(v_stx_2416_);
                            v_a_2842_ = crate::leanh::lean_ctor_get(v___x_2836_, 0);
                            v_isSharedCheck_2849_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2836_)) as u8;
                            if v_isSharedCheck_2849_ == 0 {
                                v___x_2844_ = v___x_2836_;
                                v_isShared_2845_ = v_isSharedCheck_2849_;
                                state = 19;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2842_);
                                crate::leanh::lean_dec(v___x_2836_);
                                v___x_2844_ = crate::leanh::lean_box(0);
                                v_isShared_2845_ = v_isSharedCheck_2849_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2828_);
                        crate::leanh::lean_dec(v___y_2819_);
                        crate::leanh::lean_dec(v___y_2817_);
                        crate::leanh::lean_dec(v___y_2816_);
                        crate::leanh::lean_dec_ref(v___y_2815_);
                        crate::leanh::lean_dec(v___y_2812_);
                        crate::leanh::lean_dec(v___y_2810_);
                        crate::leanh::lean_dec(v___y_2809_);
                        crate::leanh::lean_dec(v___y_2807_);
                        crate::leanh::lean_dec(v_stx_2416_);
                        v_a_2850_ = crate::leanh::lean_ctor_get(v___x_2834_, 0);
                        v_isSharedCheck_2857_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2834_)) as u8;
                        if v_isSharedCheck_2857_ == 0 {
                            v___x_2852_ = v___x_2834_;
                            v_isShared_2853_ = v_isSharedCheck_2857_;
                            state = 21;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2850_);
                            crate::leanh::lean_dec(v___x_2834_);
                            v___x_2852_ = crate::leanh::lean_box(0);
                            v_isShared_2853_ = v_isSharedCheck_2857_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2828_);
                    crate::leanh::lean_dec(v___y_2819_);
                    crate::leanh::lean_dec(v___y_2817_);
                    crate::leanh::lean_dec(v___y_2816_);
                    crate::leanh::lean_dec_ref(v___y_2815_);
                    crate::leanh::lean_dec(v___y_2812_);
                    crate::leanh::lean_dec(v___y_2810_);
                    crate::leanh::lean_dec(v___y_2809_);
                    crate::leanh::lean_dec(v___y_2807_);
                    crate::leanh::lean_dec(v_stx_2416_);
                    return v___x_2833_;
                }
            }
            19 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2847_;
            }
            21 => {
                if v_isShared_2853_ == 0 {
                    v___x_2855_ = v___x_2852_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2855_;
            }
            23 => {
                v___x_2870_ = l_Lake_DSL_mkConfigDeclIdent(v___y_2860_, v___y_2862_, v___y_2866_);
                if crate::leanh::lean_obj_tag(v___x_2870_) == 0 {
                    v_a_2871_ = crate::leanh::lean_ctor_get(v___x_2870_, 0);
                    crate::leanh::lean_inc_n(v_a_2871_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2870_, 1);
                    v___x_2872_ = lean_st_ref_get(v___y_2866_);
                    v_env_2873_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
                    crate::leanh::lean_inc_ref(v_env_2873_);
                    crate::leanh::lean_dec(v___x_2872_);
                    v___x_2874_ = l_Lake_nameExt;
                    v_asyncMode_2875_ = crate::leanh::lean_ctor_get(v___x_2874_, 2);
                    v___x_2876_ = crate::leanh::lean_box(0);
                    v___x_2877_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64;
                    v___x_2878_ =
                        l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
                            v___x_2877_,
                            v___x_2874_,
                            v_env_2873_,
                            v_asyncMode_2875_,
                            v___x_2876_,
                        );
                    v_fst_2879_ = crate::leanh::lean_ctor_get(v___x_2878_, 0);
                    crate::leanh::lean_inc(v_fst_2879_);
                    v_snd_2880_ = crate::leanh::lean_ctor_get(v___x_2878_, 1);
                    crate::leanh::lean_inc(v_snd_2880_);
                    crate::leanh::lean_dec(v___x_2878_);
                    v___x_2881_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66);
                    v___x_2882_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67;
                    v___x_2883_ = l_Lean_addMacroScope(v_a_2869_, v___x_2882_, v___y_2867_);
                    v___x_2884_ = crate::leanh::lean_box(0);
                    v___x_2885_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2885_, 0, v___y_2868_);
                    crate::leanh::lean_ctor_set(v___x_2885_, 1, v___x_2881_);
                    crate::leanh::lean_ctor_set(v___x_2885_, 2, v___x_2883_);
                    crate::leanh::lean_ctor_set(v___x_2885_, 3, v___x_2884_);
                    v___x_2886_ = l_Lean_TSyntax_getId(v_a_2871_);
                    v___x_2887_ = l_Lake_Name_quoteFrom(v_a_2871_, v___x_2886_, v___y_2859_);
                    if crate::leanh::lean_obj_tag(v_snd_2880_) == 0 {
                        crate::leanh::lean_inc(v___x_2887_);
                        v___y_2807_ = v___x_2887_;
                        v___y_2808_ = v___y_2859_;
                        v___y_2809_ = v_a_2871_;
                        v___y_2810_ = v___y_2863_;
                        v___y_2811_ = v___x_2884_;
                        v___y_2812_ = v___x_2885_;
                        v___y_2813_ = v_fst_2879_;
                        v___y_2814_ = v___y_2861_;
                        v___y_2815_ = v___y_2862_;
                        v___y_2816_ = v___y_2864_;
                        v___y_2817_ = v___y_2865_;
                        v___y_2818_ = v___y_2866_;
                        v___y_2819_ = v___x_2887_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2871_);
                        v___x_2888_ = l_Lake_Name_quoteFrom(v_a_2871_, v_snd_2880_, v___y_2859_);
                        v___y_2807_ = v___x_2887_;
                        v___y_2808_ = v___y_2859_;
                        v___y_2809_ = v_a_2871_;
                        v___y_2810_ = v___y_2863_;
                        v___y_2811_ = v___x_2884_;
                        v___y_2812_ = v___x_2885_;
                        v___y_2813_ = v_fst_2879_;
                        v___y_2814_ = v___y_2861_;
                        v___y_2815_ = v___y_2862_;
                        v___y_2816_ = v___y_2864_;
                        v___y_2817_ = v___y_2865_;
                        v___y_2818_ = v___y_2866_;
                        v___y_2819_ = v___x_2888_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2869_);
                    crate::leanh::lean_dec(v___y_2868_);
                    crate::leanh::lean_dec(v___y_2867_);
                    crate::leanh::lean_dec(v___y_2865_);
                    crate::leanh::lean_dec(v___y_2864_);
                    crate::leanh::lean_dec(v___y_2863_);
                    crate::leanh::lean_dec_ref(v___y_2862_);
                    crate::leanh::lean_dec(v___y_2861_);
                    crate::leanh::lean_dec(v_stx_2416_);
                    v_a_2889_ = crate::leanh::lean_ctor_get(v___x_2870_, 0);
                    v_isSharedCheck_2896_ = (!crate::leanh::lean_is_exclusive(v___x_2870_)) as u8;
                    if v_isSharedCheck_2896_ == 0 {
                        v___x_2891_ = v___x_2870_;
                        v_isShared_2892_ = v_isSharedCheck_2896_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2889_);
                        crate::leanh::lean_dec(v___x_2870_);
                        v___x_2891_ = crate::leanh::lean_box(0);
                        v_isShared_2892_ = v_isSharedCheck_2896_;
                        state = 24;
                        continue;
                    }
                }
            }
            24 => {
                if v_isShared_2892_ == 0 {
                    v___x_2894_ = v___x_2891_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
                    v___x_2894_ = v_reuseFailAlloc_2895_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2894_;
            }
            26 => {
                v___x_2905_ = l_Lean_Elab_Command_getRef___redArg(v___y_2899_);
                if crate::leanh::lean_obj_tag(v___x_2905_) == 0 {
                    v_a_2906_ = crate::leanh::lean_ctor_get(v___x_2905_, 0);
                    crate::leanh::lean_inc(v_a_2906_);
                    crate::leanh::lean_dec_ref_known(v___x_2905_, 1);
                    v_fileName_2907_ = crate::leanh::lean_ctor_get(v___y_2899_, 0);
                    v_fileMap_2908_ = crate::leanh::lean_ctor_get(v___y_2899_, 1);
                    v_currRecDepth_2909_ = crate::leanh::lean_ctor_get(v___y_2899_, 2);
                    v_cmdPos_2910_ = crate::leanh::lean_ctor_get(v___y_2899_, 3);
                    v_macroStack_2911_ = crate::leanh::lean_ctor_get(v___y_2899_, 4);
                    v_quotContext_x3f_2912_ = crate::leanh::lean_ctor_get(v___y_2899_, 5);
                    v_currMacroScope_2913_ = crate::leanh::lean_ctor_get(v___y_2899_, 6);
                    v_snap_x3f_2914_ = crate::leanh::lean_ctor_get(v___y_2899_, 8);
                    v_cancelTk_x3f_2915_ = crate::leanh::lean_ctor_get(v___y_2899_, 9);
                    v_suppressElabErrors_2916_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2899_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_2917_ = l_Lean_replaceRef(v_kw_2897_, v_a_2906_);
                    crate::leanh::lean_dec(v_a_2906_);
                    crate::leanh::lean_dec(v_kw_2897_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_2915_);
                    crate::leanh::lean_inc(v_snap_x3f_2914_);
                    crate::leanh::lean_inc(v_currMacroScope_2913_);
                    crate::leanh::lean_inc(v_quotContext_x3f_2912_);
                    crate::leanh::lean_inc(v_macroStack_2911_);
                    crate::leanh::lean_inc(v_cmdPos_2910_);
                    crate::leanh::lean_inc(v_currRecDepth_2909_);
                    crate::leanh::lean_inc_ref(v_fileMap_2908_);
                    crate::leanh::lean_inc_ref(v_fileName_2907_);
                    v___x_2918_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_2918_, 0, v_fileName_2907_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 1, v_fileMap_2908_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 2, v_currRecDepth_2909_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 3, v_cmdPos_2910_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 4, v_macroStack_2911_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 5, v_quotContext_x3f_2912_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 6, v_currMacroScope_2913_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 7, v_ref_2917_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 8, v_snap_x3f_2914_);
                    crate::leanh::lean_ctor_set(v___x_2918_, 9, v_cancelTk_x3f_2915_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_2918_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2916_,
                    );
                    v___x_2919_ = l_Lean_Elab_Command_getRef___redArg(v___x_2918_);
                    if crate::leanh::lean_obj_tag(v___x_2919_) == 0 {
                        v_a_2920_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
                        crate::leanh::lean_inc(v_a_2920_);
                        crate::leanh::lean_dec_ref_known(v___x_2919_, 1);
                        v___x_2921_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_2918_);
                        if crate::leanh::lean_obj_tag(v___x_2921_) == 0 {
                            v_a_2922_ = crate::leanh::lean_ctor_get(v___x_2921_, 0);
                            crate::leanh::lean_inc(v_a_2922_);
                            crate::leanh::lean_dec_ref_known(v___x_2921_, 1);
                            v___x_2923_ = 0;
                            v___x_2924_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_2923_);
                            crate::leanh::lean_dec(v_a_2920_);
                            if crate::leanh::lean_obj_tag(v_quotContext_x3f_2912_) == 0 {
                                v___x_2925_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2903_);
                                v_a_2926_ = crate::leanh::lean_ctor_get(v___x_2925_, 0);
                                crate::leanh::lean_inc(v_a_2926_);
                                crate::leanh::lean_dec_ref(v___x_2925_);
                                v___y_2859_ = v___x_2923_;
                                v___y_2860_ = v___y_2900_;
                                v___y_2861_ = v___y_2901_;
                                v___y_2862_ = v___x_2918_;
                                v___y_2863_ = v_quotContext_x3f_2912_;
                                v___y_2864_ = v___y_2904_;
                                v___y_2865_ = v___y_2902_;
                                v___y_2866_ = v___y_2903_;
                                v___y_2867_ = v_a_2922_;
                                v___y_2868_ = v___x_2924_;
                                v_a_2869_ = v_a_2926_;
                                state = 23;
                                continue;
                            } else {
                                v_val_2927_ =
                                    crate::leanh::lean_ctor_get(v_quotContext_x3f_2912_, 0);
                                crate::leanh::lean_inc(v_val_2927_);
                                crate::leanh::lean_inc_ref(v_quotContext_x3f_2912_);
                                v___y_2859_ = v___x_2923_;
                                v___y_2860_ = v___y_2900_;
                                v___y_2861_ = v___y_2901_;
                                v___y_2862_ = v___x_2918_;
                                v___y_2863_ = v_quotContext_x3f_2912_;
                                v___y_2864_ = v___y_2904_;
                                v___y_2865_ = v___y_2902_;
                                v___y_2866_ = v___y_2903_;
                                v___y_2867_ = v_a_2922_;
                                v___y_2868_ = v___x_2924_;
                                v_a_2869_ = v_val_2927_;
                                state = 23;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2920_);
                            crate::leanh::lean_dec_ref_known(v___x_2918_, 10);
                            crate::leanh::lean_dec(v___y_2904_);
                            crate::leanh::lean_dec(v___y_2902_);
                            crate::leanh::lean_dec(v___y_2901_);
                            crate::leanh::lean_dec(v___y_2900_);
                            crate::leanh::lean_dec(v_stx_2416_);
                            v_a_2928_ = crate::leanh::lean_ctor_get(v___x_2921_, 0);
                            v_isSharedCheck_2935_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2921_)) as u8;
                            if v_isSharedCheck_2935_ == 0 {
                                v___x_2930_ = v___x_2921_;
                                v_isShared_2931_ = v_isSharedCheck_2935_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2928_);
                                crate::leanh::lean_dec(v___x_2921_);
                                v___x_2930_ = crate::leanh::lean_box(0);
                                v_isShared_2931_ = v_isSharedCheck_2935_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2918_, 10);
                        crate::leanh::lean_dec(v___y_2904_);
                        crate::leanh::lean_dec(v___y_2902_);
                        crate::leanh::lean_dec(v___y_2901_);
                        crate::leanh::lean_dec(v___y_2900_);
                        crate::leanh::lean_dec(v_stx_2416_);
                        v_a_2936_ = crate::leanh::lean_ctor_get(v___x_2919_, 0);
                        v_isSharedCheck_2943_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2943_ == 0 {
                            v___x_2938_ = v___x_2919_;
                            v_isShared_2939_ = v_isSharedCheck_2943_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2936_);
                            crate::leanh::lean_dec(v___x_2919_);
                            v___x_2938_ = crate::leanh::lean_box(0);
                            v_isShared_2939_ = v_isSharedCheck_2943_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2904_);
                    crate::leanh::lean_dec(v___y_2902_);
                    crate::leanh::lean_dec(v___y_2901_);
                    crate::leanh::lean_dec(v___y_2900_);
                    crate::leanh::lean_dec(v_kw_2897_);
                    crate::leanh::lean_dec(v_stx_2416_);
                    v_a_2944_ = crate::leanh::lean_ctor_get(v___x_2905_, 0);
                    v_isSharedCheck_2951_ = (!crate::leanh::lean_is_exclusive(v___x_2905_)) as u8;
                    if v_isSharedCheck_2951_ == 0 {
                        v___x_2946_ = v___x_2905_;
                        v_isShared_2947_ = v_isSharedCheck_2951_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2944_);
                        crate::leanh::lean_dec(v___x_2905_);
                        v___x_2946_ = crate::leanh::lean_box(0);
                        v_isShared_2947_ = v_isSharedCheck_2951_;
                        state = 31;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_2931_ == 0 {
                    v___x_2933_ = v___x_2930_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
                    v___x_2933_ = v_reuseFailAlloc_2934_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_2933_;
            }
            29 => {
                if v_isShared_2939_ == 0 {
                    v___x_2941_ = v___x_2938_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_2942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
                    v___x_2941_ = v_reuseFailAlloc_2942_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_2941_;
            }
            31 => {
                if v_isShared_2947_ == 0 {
                    v___x_2949_ = v___x_2946_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
                    v___x_2949_ = v_reuseFailAlloc_2950_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_2949_;
            }
            33 => {
                v___x_2958_ = l_Lean_Syntax_getOptional_x3f(v___x_2493_);
                crate::leanh::lean_dec(v___x_2493_);
                if crate::leanh::lean_obj_tag(v___x_2958_) == 0 {
                    v___x_2959_ = crate::leanh::lean_box(0);
                    v___y_2899_ = v___y_2953_;
                    v___y_2900_ = v___y_2954_;
                    v___y_2901_ = v___y_2955_;
                    v___y_2902_ = v___y_2957_;
                    v___y_2903_ = v___y_2956_;
                    v___y_2904_ = v___x_2959_;
                    state = 26;
                    continue;
                } else {
                    v_val_2960_ = crate::leanh::lean_ctor_get(v___x_2958_, 0);
                    v_isSharedCheck_2967_ = (!crate::leanh::lean_is_exclusive(v___x_2958_)) as u8;
                    if v_isSharedCheck_2967_ == 0 {
                        v___x_2962_ = v___x_2958_;
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2960_);
                        crate::leanh::lean_dec(v___x_2958_);
                        v___x_2962_ = crate::leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 34;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_2963_ == 0 {
                    v___x_2965_ = v___x_2962_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_val_2960_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                v___y_2899_ = v___y_2953_;
                v___y_2900_ = v___y_2954_;
                v___y_2901_ = v___y_2955_;
                v___y_2902_ = v___y_2957_;
                v___y_2903_ = v___y_2956_;
                v___y_2904_ = v___x_2965_;
                state = 26;
                continue;
            }
            36 => {
                v___x_2972_ = crate::leanh::lean_unsigned_to_nat(4);
                v_cfg_2973_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2972_);
                v___x_2974_ = l_Lean_Syntax_getOptional_x3f(v___x_2495_);
                crate::leanh::lean_dec(v___x_2495_);
                if crate::leanh::lean_obj_tag(v___x_2974_) == 0 {
                    v___x_2975_ = crate::leanh::lean_box(0);
                    v___y_2953_ = v___y_2970_;
                    v___y_2954_ = v_nameStx_x3f_2969_;
                    v___y_2955_ = v_cfg_2973_;
                    v___y_2956_ = v___y_2971_;
                    v___y_2957_ = v___x_2975_;
                    state = 33;
                    continue;
                } else {
                    v_val_2976_ = crate::leanh::lean_ctor_get(v___x_2974_, 0);
                    v_isSharedCheck_2983_ = (!crate::leanh::lean_is_exclusive(v___x_2974_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v___x_2978_ = v___x_2974_;
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2976_);
                        crate::leanh::lean_dec(v___x_2974_);
                        v___x_2978_ = crate::leanh::lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 37;
                        continue;
                    }
                }
            }
            37 => {
                if v_isShared_2979_ == 0 {
                    v___x_2981_ = v___x_2978_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_2982_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_val_2976_);
                    v___x_2981_ = v_reuseFailAlloc_2982_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___y_2953_ = v___y_2970_;
                v___y_2954_ = v_nameStx_x3f_2969_;
                v___y_2955_ = v_cfg_2973_;
                v___y_2956_ = v___y_2971_;
                v___y_2957_ = v___x_2981_;
                state = 33;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed(
    mut v_stx_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2997_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(
        v_stx_2993_,
        v_a_2994_,
        v_a_2995_,
    );
    crate::leanh::lean_dec(v_a_2995_);
    crate::leanh::lean_dec_ref(v_a_2994_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(
    mut v_00_u03b1_2998_: *mut crate::leanh::LeanObject,
    mut v_ref_2999_: *mut crate::leanh::LeanObject,
    mut v_msg_3000_: *mut crate::leanh::LeanObject,
    mut v___y_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3004_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_2999_, v_msg_3000_, v___y_3001_, v___y_3002_);
    return v___x_3004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(
    mut v_00_u03b1_3005_: *mut crate::leanh::LeanObject,
    mut v_ref_3006_: *mut crate::leanh::LeanObject,
    mut v_msg_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
    mut v___y_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3011_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_3005_, v_ref_3006_, v_msg_3007_, v___y_3008_, v___y_3009_);
    crate::leanh::lean_dec(v___y_3009_);
    crate::leanh::lean_dec_ref(v___y_3008_);
    crate::leanh::lean_dec(v_ref_3006_);
    return v_res_3011_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(
    mut v_msgData_3012_: *mut crate::leanh::LeanObject,
    mut v___y_3013_: *mut crate::leanh::LeanObject,
    mut v___y_3014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3016_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_3012_, v___y_3014_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_3017_: *mut crate::leanh::LeanObject,
    mut v___y_3018_: *mut crate::leanh::LeanObject,
    mut v___y_3019_: *mut crate::leanh::LeanObject,
    mut v___y_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_3017_, v___y_3018_, v___y_3019_);
    crate::leanh::lean_dec(v___y_3019_);
    crate::leanh::lean_dec_ref(v___y_3018_);
    return v_res_3021_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(
    mut v_00_u03b1_3022_: *mut crate::leanh::LeanObject,
    mut v_msg_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_3023_, v___y_3024_, v___y_3025_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(
    mut v_00_u03b1_3028_: *mut crate::leanh::LeanObject,
    mut v_msg_3029_: *mut crate::leanh::LeanObject,
    mut v___y_3030_: *mut crate::leanh::LeanObject,
    mut v___y_3031_: *mut crate::leanh::LeanObject,
    mut v___y_3032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_3028_, v_msg_3029_, v___y_3030_, v___y_3031_);
    crate::leanh::lean_dec(v___y_3031_);
    crate::leanh::lean_dec_ref(v___y_3030_);
    return v_res_3033_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(
    mut v_msgData_3034_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3035_: *mut crate::leanh::LeanObject,
    mut v___y_3036_: *mut crate::leanh::LeanObject,
    mut v___y_3037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3039_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_3034_, v_macroStack_3035_, v___y_3037_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(
    mut v_msgData_3040_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3041_: *mut crate::leanh::LeanObject,
    mut v___y_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_3040_, v_macroStack_3041_, v___y_3042_, v___y_3043_);
    crate::leanh::lean_dec(v___y_3043_);
    crate::leanh::lean_dec_ref(v___y_3042_);
    return v_res_3045_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3074_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3075_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12;
    v___x_3076_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10;
    v___x_3077_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___boxed
            as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3078_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3074_,
        v___x_3075_,
        v___x_3076_,
        v___x_3077_,
    );
    return v___x_3078_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___boxed(
    mut v_a_3079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3080_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
    return v_res_3080_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3088_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3;
    v___x_3089_ = l_String_toRawSubstring_x27(v___x_3088_);
    return v___x_3089_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6;
    v___x_3094_ = l_String_toRawSubstring_x27(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12;
    v___x_3107_ = l_String_toRawSubstring_x27(v___x_3106_);
    return v___x_3107_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3111_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15;
    v___x_3112_ = l_String_toRawSubstring_x27(v___x_3111_);
    return v___x_3112_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3119_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21;
    v___x_3120_ = l_String_toRawSubstring_x27(v___x_3119_);
    return v___x_3120_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(
    mut v_stx_3145_: *mut crate::leanh::LeanObject,
    mut v_a_3146_: *mut crate::leanh::LeanObject,
    mut v_a_3147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3329_: u8 = 0;
    let mut v_wds_x3f_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_x3f_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: u8 = 0;
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kw_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pkg_x3f_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3171_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1;
                crate::leanh::lean_inc(v_stx_3145_);
                v___x_3191_ = l_Lean_Syntax_isOfKind(v_stx_3145_, v___x_3171_);
                if v___x_3191_ == 0 {
                    v___x_3192_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                    v___x_3193_ = l_Lean_Macro_throwErrorAt___redArg(
                        v_stx_3145_,
                        v___x_3192_,
                        v_a_3146_,
                        v_a_3147_,
                    );
                    crate::leanh::lean_dec(v_stx_3145_);
                    return v___x_3193_;
                } else {
                    v___x_3194_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3578_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3194_);
                    v___x_3579_ = l_Lean_Syntax_isNone(v___x_3578_);
                    if v___x_3579_ == 0 {
                        v___x_3580_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_3578_);
                        v___x_3581_ = l_Lean_Syntax_matchesNull(v___x_3578_, v___x_3580_);
                        if v___x_3581_ == 0 {
                            crate::leanh::lean_dec(v___x_3578_);
                            v___x_3582_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                            v___x_3583_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_3145_,
                                v___x_3582_,
                                v_a_3146_,
                                v_a_3147_,
                            );
                            crate::leanh::lean_dec(v_stx_3145_);
                            return v___x_3583_;
                        } else {
                            v_doc_x3f_3584_ = l_Lean_Syntax_getArg(v___x_3578_, v___x_3194_);
                            crate::leanh::lean_dec(v___x_3578_);
                            v___x_3585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3585_, 0, v_doc_x3f_3584_);
                            v_doc_x3f_3566_ = v___x_3585_;
                            v___y_3567_ = v_a_3146_;
                            v___y_3568_ = v_a_3147_;
                            state = 13;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3578_);
                        v___x_3586_ = crate::leanh::lean_box(0);
                        v_doc_x3f_3566_ = v___x_3586_;
                        v___y_3567_ = v_a_3146_;
                        v___y_3568_ = v_a_3147_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_3154_);
                v___x_3165_ = l_Array_append___redArg(v___y_3154_, v___y_3164_);
                crate::leanh::lean_dec_ref(v___y_3164_);
                crate::leanh::lean_inc(v___y_3163_);
                crate::leanh::lean_inc_n(v___y_3159_, 3);
                v___x_3166_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3166_, 0, v___y_3159_);
                crate::leanh::lean_ctor_set(v___x_3166_, 1, v___y_3163_);
                crate::leanh::lean_ctor_set(v___x_3166_, 2, v___x_3165_);
                crate::leanh::lean_inc(v___y_3155_);
                v___x_3167_ = l_Lean_Syntax_node4(
                    v___y_3159_,
                    v___y_3155_,
                    v___y_3149_,
                    v___y_3151_,
                    v___y_3160_,
                    v___x_3166_,
                );
                v___x_3168_ = l_Lean_Syntax_node5(
                    v___y_3159_,
                    v___y_3158_,
                    v___y_3157_,
                    v___y_3152_,
                    v___y_3150_,
                    v___x_3167_,
                    v___y_3153_,
                );
                v___x_3169_ =
                    l_Lean_Syntax_node2(v___y_3159_, v___y_3161_, v___y_3162_, v___x_3168_);
                v___x_3170_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3170_, 0, v___x_3169_);
                crate::leanh::lean_ctor_set(v___x_3170_, 1, v___y_3156_);
                return v___x_3170_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_3184_);
                v___x_3186_ = l_Array_append___redArg(v___y_3184_, v___y_3185_);
                crate::leanh::lean_dec_ref(v___y_3185_);
                crate::leanh::lean_inc(v___y_3178_);
                crate::leanh::lean_inc_n(v___y_3175_, 2);
                v___x_3187_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3187_, 0, v___y_3175_);
                crate::leanh::lean_ctor_set(v___x_3187_, 1, v___y_3178_);
                crate::leanh::lean_ctor_set(v___x_3187_, 2, v___x_3186_);
                v___x_3188_ = l_Lean_Syntax_node4(
                    v___y_3175_,
                    v___y_3173_,
                    v___y_3177_,
                    v___y_3174_,
                    v___y_3176_,
                    v___x_3187_,
                );
                v___x_3189_ = l_Lean_Syntax_node5(
                    v___y_3175_,
                    v___x_3171_,
                    v___y_3180_,
                    v___y_3182_,
                    v___y_3181_,
                    v___y_3183_,
                    v___x_3188_,
                );
                v___x_3190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3189_);
                crate::leanh::lean_ctor_set(v___x_3190_, 1, v___y_3179_);
                return v___x_3190_;
            }
            3 => {
                crate::leanh::lean_inc_ref_n(v___y_3203_, 2);
                v___x_3217_ = l_Array_append___redArg(v___y_3203_, v___y_3216_);
                crate::leanh::lean_dec_ref(v___y_3216_);
                crate::leanh::lean_inc_n(v___y_3214_, 8);
                crate::leanh::lean_inc_n(v___y_3210_, 41);
                v___x_3218_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3218_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3218_, 1, v___y_3214_);
                crate::leanh::lean_ctor_set(v___x_3218_, 2, v___x_3217_);
                v___x_3219_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15;
                crate::leanh::lean_inc_ref_n(v___y_3208_, 9);
                crate::leanh::lean_inc_ref_n(v___y_3207_, 13);
                crate::leanh::lean_inc_ref_n(v___y_3201_, 13);
                v___x_3220_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3219_);
                v___x_3221_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16;
                v___x_3222_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3222_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3222_, 1, v___x_3221_);
                v___x_3223_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39;
                v___x_3224_ = l_Lean_Syntax_SepArray_ofElems(v___x_3223_, v___y_3211_);
                crate::leanh::lean_dec_ref(v___y_3211_);
                v___x_3225_ = l_Array_append___redArg(v___y_3203_, v___x_3224_);
                crate::leanh::lean_dec_ref(v___x_3224_);
                v___x_3226_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3226_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3226_, 1, v___y_3214_);
                crate::leanh::lean_ctor_set(v___x_3226_, 2, v___x_3225_);
                v___x_3227_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17;
                v___x_3228_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3228_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3228_, 1, v___x_3227_);
                v___x_3229_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___x_3220_,
                    v___x_3222_,
                    v___x_3226_,
                    v___x_3228_,
                );
                v___x_3230_ = l_Lean_Syntax_node1(v___y_3210_, v___y_3214_, v___x_3229_);
                crate::leanh::lean_inc_n(v___y_3202_, 21);
                v___x_3231_ = l_Lean_Syntax_node7(
                    v___y_3210_,
                    v___y_3199_,
                    v___x_3218_,
                    v___x_3230_,
                    v___y_3202_,
                    v___y_3202_,
                    v___y_3202_,
                    v___y_3202_,
                    v___y_3202_,
                );
                v___x_3232_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5;
                crate::leanh::lean_inc_ref_n(v___y_3200_, 3);
                v___x_3233_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3200_, v___x_3232_);
                v___x_3234_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6;
                v___x_3235_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3235_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                v___x_3236_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7;
                v___x_3237_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3200_, v___x_3236_);
                v___x_3238_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
                v___x_3239_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5;
                crate::leanh::lean_inc_n(v___y_3212_, 3);
                crate::leanh::lean_inc_n(v___y_3197_, 3);
                v___x_3240_ = l_Lean_addMacroScope(v___y_3197_, v___x_3239_, v___y_3212_);
                crate::leanh::lean_inc_n(v___y_3198_, 4);
                v___x_3241_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3241_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3241_, 1, v___x_3238_);
                crate::leanh::lean_ctor_set(v___x_3241_, 2, v___x_3240_);
                crate::leanh::lean_ctor_set(v___x_3241_, 3, v___y_3198_);
                v___x_3242_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3237_, v___x_3241_, v___y_3202_);
                v___x_3243_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9;
                v___x_3244_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3200_, v___x_3243_);
                v___x_3245_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11;
                v___x_3246_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3245_);
                v___x_3247_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12;
                v___x_3248_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3248_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3248_, 1, v___x_3247_);
                v___x_3249_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
                v___x_3250_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8;
                v___x_3251_ = l_Lean_addMacroScope(v___y_3197_, v___x_3250_, v___y_3212_);
                v___x_3252_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10;
                v___x_3253_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11;
                v___x_3254_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3254_, 0, v___x_3253_);
                crate::leanh::lean_ctor_set(v___x_3254_, 1, v___y_3198_);
                v___x_3255_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3255_, 0, v___x_3252_);
                crate::leanh::lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                v___x_3256_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3256_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3256_, 1, v___x_3249_);
                crate::leanh::lean_ctor_set(v___x_3256_, 2, v___x_3251_);
                crate::leanh::lean_ctor_set(v___x_3256_, 3, v___x_3255_);
                v___x_3257_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3246_, v___x_3248_, v___x_3256_);
                v___x_3258_ = l_Lean_Syntax_node1(v___y_3210_, v___y_3214_, v___x_3257_);
                v___x_3259_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3244_, v___y_3202_, v___x_3258_);
                v___x_3260_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38;
                v___x_3261_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3261_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3261_, 1, v___x_3260_);
                v___x_3262_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30;
                v___x_3263_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3262_);
                v___x_3264_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31;
                v___x_3265_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3265_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3265_, 1, v___x_3264_);
                v___x_3266_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31;
                v___x_3267_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3266_);
                v___x_3268_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32;
                v___x_3269_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3268_);
                v___x_3270_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33;
                v___x_3271_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3270_);
                v___x_3272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
                v___x_3273_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14;
                v___x_3274_ = l_Lean_addMacroScope(v___y_3197_, v___x_3273_, v___y_3212_);
                v___x_3275_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3275_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3275_, 1, v___x_3272_);
                crate::leanh::lean_ctor_set(v___x_3275_, 2, v___x_3274_);
                crate::leanh::lean_ctor_set(v___x_3275_, 3, v___y_3198_);
                crate::leanh::lean_inc(v___x_3271_);
                v___x_3276_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3271_, v___x_3275_, v___y_3202_);
                v___x_3277_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37;
                v___x_3278_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3277_);
                v___x_3279_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9;
                v___x_3280_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10;
                v___x_3281_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3281_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3281_, 1, v___x_3280_);
                v___x_3282_ = l_Lean_Syntax_node1(v___y_3210_, v___x_3279_, v___x_3281_);
                crate::leanh::lean_inc_ref_n(v___x_3261_, 2);
                crate::leanh::lean_inc(v___x_3278_);
                v___x_3283_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___x_3278_,
                    v___x_3261_,
                    v___y_3202_,
                    v___x_3282_,
                );
                v___x_3284_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___y_3214_,
                    v___y_3202_,
                    v___y_3202_,
                    v___x_3283_,
                );
                crate::leanh::lean_inc(v___x_3269_);
                v___x_3285_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3269_, v___x_3276_, v___x_3284_);
                v___x_3286_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3286_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3286_, 1, v___x_3223_);
                v___x_3287_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
                v___x_3288_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17;
                v___x_3289_ = l_Lean_addMacroScope(v___y_3197_, v___x_3288_, v___y_3212_);
                v___x_3290_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3290_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3290_, 1, v___x_3287_);
                crate::leanh::lean_ctor_set(v___x_3290_, 2, v___x_3289_);
                crate::leanh::lean_ctor_set(v___x_3290_, 3, v___y_3198_);
                v___x_3291_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3271_, v___x_3290_, v___y_3202_);
                v___x_3292_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18;
                v___x_3293_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3292_);
                v___x_3294_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3294_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3294_, 1, v___x_3292_);
                v___x_3295_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19;
                v___x_3296_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3295_);
                v___x_3297_ = l_Lean_Syntax_node1(v___y_3210_, v___y_3214_, v___y_3205_);
                v___x_3298_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20;
                v___x_3299_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3299_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3299_, 1, v___x_3298_);
                v___x_3300_ = l_Lean_Syntax_node4(
                    v___y_3210_,
                    v___x_3296_,
                    v___x_3297_,
                    v___y_3202_,
                    v___x_3299_,
                    v___y_3196_,
                );
                v___x_3301_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3293_, v___x_3294_, v___x_3300_);
                v___x_3302_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___x_3278_,
                    v___x_3261_,
                    v___y_3202_,
                    v___x_3301_,
                );
                v___x_3303_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___y_3214_,
                    v___y_3202_,
                    v___y_3202_,
                    v___x_3302_,
                );
                v___x_3304_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3269_, v___x_3291_, v___x_3303_);
                v___x_3305_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___y_3214_,
                    v___x_3285_,
                    v___x_3286_,
                    v___x_3304_,
                );
                v___x_3306_ = l_Lean_Syntax_node1(v___y_3210_, v___x_3267_, v___x_3305_);
                v___x_3307_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49;
                v___x_3308_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3307_);
                v___x_3309_ = l_Lean_Syntax_node1(v___y_3210_, v___x_3308_, v___y_3202_);
                v___x_3310_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50;
                v___x_3311_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3311_, 0, v___y_3210_);
                crate::leanh::lean_ctor_set(v___x_3311_, 1, v___x_3310_);
                v___x_3312_ = l_Lean_Syntax_node6(
                    v___y_3210_,
                    v___x_3263_,
                    v___x_3265_,
                    v___y_3202_,
                    v___x_3306_,
                    v___x_3309_,
                    v___y_3202_,
                    v___x_3311_,
                );
                crate::leanh::lean_inc(v___y_3209_);
                v___x_3313_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___y_3209_, v___y_3202_, v___y_3202_);
                if crate::leanh::lean_obj_tag(v___y_3215_) == 1 {
                    v_val_3314_ = crate::leanh::lean_ctor_get(v___y_3215_, 0);
                    crate::leanh::lean_inc(v_val_3314_);
                    crate::leanh::lean_dec_ref_known(v___y_3215_, 1);
                    v___x_3315_ = l_Array_mkArray1___redArg(v_val_3314_);
                    v___y_3149_ = v___x_3261_;
                    v___y_3150_ = v___x_3259_;
                    v___y_3151_ = v___x_3312_;
                    v___y_3152_ = v___x_3242_;
                    v___y_3153_ = v___y_3202_;
                    v___y_3154_ = v___y_3203_;
                    v___y_3155_ = v___y_3204_;
                    v___y_3156_ = v___y_3206_;
                    v___y_3157_ = v___x_3235_;
                    v___y_3158_ = v___x_3233_;
                    v___y_3159_ = v___y_3210_;
                    v___y_3160_ = v___x_3313_;
                    v___y_3161_ = v___y_3213_;
                    v___y_3162_ = v___x_3231_;
                    v___y_3163_ = v___y_3214_;
                    v___y_3164_ = v___x_3315_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3215_);
                    v___x_3316_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                    v___y_3149_ = v___x_3261_;
                    v___y_3150_ = v___x_3259_;
                    v___y_3151_ = v___x_3312_;
                    v___y_3152_ = v___x_3242_;
                    v___y_3153_ = v___y_3202_;
                    v___y_3154_ = v___y_3203_;
                    v___y_3155_ = v___y_3204_;
                    v___y_3156_ = v___y_3206_;
                    v___y_3157_ = v___x_3235_;
                    v___y_3158_ = v___x_3233_;
                    v___y_3159_ = v___y_3210_;
                    v___y_3160_ = v___x_3313_;
                    v___y_3161_ = v___y_3213_;
                    v___y_3162_ = v___x_3231_;
                    v___y_3163_ = v___y_3214_;
                    v___y_3164_ = v___x_3316_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v_methods_3333_ = crate::leanh::lean_ctor_get(v___y_3331_, 0);
                v_quotContext_3334_ = crate::leanh::lean_ctor_get(v___y_3331_, 1);
                v_currMacroScope_3335_ = crate::leanh::lean_ctor_get(v___y_3331_, 2);
                v_currRecDepth_3336_ = crate::leanh::lean_ctor_get(v___y_3331_, 3);
                v_maxRecDepth_3337_ = crate::leanh::lean_ctor_get(v___y_3331_, 4);
                v_ref_3338_ = crate::leanh::lean_ctor_get(v___y_3331_, 5);
                v_ref_3339_ = l_Lean_replaceRef(v___y_3326_, v_ref_3338_);
                crate::leanh::lean_dec(v___y_3326_);
                crate::leanh::lean_inc(v_ref_3339_);
                crate::leanh::lean_inc(v_maxRecDepth_3337_);
                crate::leanh::lean_inc(v_currRecDepth_3336_);
                crate::leanh::lean_inc(v_currMacroScope_3335_);
                crate::leanh::lean_inc(v_quotContext_3334_);
                crate::leanh::lean_inc(v_methods_3333_);
                v___x_3340_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3340_, 0, v_methods_3333_);
                crate::leanh::lean_ctor_set(v___x_3340_, 1, v_quotContext_3334_);
                crate::leanh::lean_ctor_set(v___x_3340_, 2, v_currMacroScope_3335_);
                crate::leanh::lean_ctor_set(v___x_3340_, 3, v_currRecDepth_3336_);
                crate::leanh::lean_ctor_set(v___x_3340_, 4, v_maxRecDepth_3337_);
                crate::leanh::lean_ctor_set(v___x_3340_, 5, v_ref_3339_);
                v___x_3341_ =
                    l_Lake_DSL_expandOptSimpleBinder(v___y_3323_, v___x_3340_, v___y_3332_);
                crate::leanh::lean_dec_ref_known(v___x_3340_, 6);
                if crate::leanh::lean_obj_tag(v___x_3341_) == 0 {
                    v_a_3342_ = crate::leanh::lean_ctor_get(v___x_3341_, 0);
                    crate::leanh::lean_inc(v_a_3342_);
                    v_a_3343_ = crate::leanh::lean_ctor_get(v___x_3341_, 1);
                    crate::leanh::lean_inc(v_a_3343_);
                    crate::leanh::lean_dec_ref_known(v___x_3341_, 2);
                    v___x_3344_ = l_Lean_SourceInfo_fromRef(v_ref_3339_, v___y_3329_);
                    crate::leanh::lean_dec(v_ref_3339_);
                    v___x_3345_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10;
                    v___x_3346_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51;
                    crate::leanh::lean_inc_ref_n(v___y_3322_, 5);
                    crate::leanh::lean_inc_ref_n(v___y_3327_, 5);
                    v___x_3347_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___x_3345_, v___x_3346_);
                    v___x_3348_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52;
                    v___x_3349_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___x_3345_, v___x_3348_);
                    v___x_3350_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                    v___x_3351_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                    crate::leanh::lean_inc_n(v___x_3344_, 5);
                    v___x_3352_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3344_);
                    crate::leanh::lean_ctor_set(v___x_3352_, 1, v___x_3350_);
                    crate::leanh::lean_ctor_set(v___x_3352_, 2, v___x_3351_);
                    crate::leanh::lean_inc_ref_n(v___x_3352_, 2);
                    v___x_3353_ = l_Lean_Syntax_node1(v___x_3344_, v___x_3349_, v___x_3352_);
                    v___x_3354_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57;
                    v___x_3355_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58;
                    v___x_3356_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___x_3354_, v___x_3355_);
                    v___x_3357_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
                    v___x_3358_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24;
                    crate::leanh::lean_inc(v_currMacroScope_3335_);
                    crate::leanh::lean_inc(v_quotContext_3334_);
                    v___x_3359_ = l_Lean_addMacroScope(
                        v_quotContext_3334_,
                        v___x_3358_,
                        v_currMacroScope_3335_,
                    );
                    v___x_3360_ = crate::leanh::lean_box(0);
                    v___x_3361_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3361_, 0, v___x_3344_);
                    crate::leanh::lean_ctor_set(v___x_3361_, 1, v___x_3357_);
                    crate::leanh::lean_ctor_set(v___x_3361_, 2, v___x_3359_);
                    crate::leanh::lean_ctor_set(v___x_3361_, 3, v___x_3360_);
                    v___x_3362_ =
                        l_Lean_Syntax_node2(v___x_3344_, v___x_3356_, v___x_3361_, v___x_3352_);
                    v___x_3363_ =
                        l_Lean_Syntax_node2(v___x_3344_, v___x_3347_, v___x_3353_, v___x_3362_);
                    v___x_3364_ = lean_mk_empty_array_with_capacity(v___y_3328_);
                    v___x_3365_ = lean_array_push(v___x_3364_, v___x_3363_);
                    v___x_3366_ = l_Lake_DSL_expandAttrs(v___y_3321_);
                    v___x_3367_ = l_Array_append___redArg(v___x_3365_, v___x_3366_);
                    crate::leanh::lean_dec_ref(v___x_3366_);
                    v___x_3368_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0;
                    crate::leanh::lean_inc_ref_n(v___y_3324_, 2);
                    v___x_3369_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___y_3324_, v___x_3368_);
                    v___x_3370_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1;
                    v___x_3371_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___y_3324_, v___x_3370_);
                    if crate::leanh::lean_obj_tag(v___y_3318_) == 1 {
                        v_val_3372_ = crate::leanh::lean_ctor_get(v___y_3318_, 0);
                        crate::leanh::lean_inc(v_val_3372_);
                        crate::leanh::lean_dec_ref_known(v___y_3318_, 1);
                        v___x_3373_ = l_Array_mkArray1___redArg(v_val_3372_);
                        crate::leanh::lean_inc(v_currMacroScope_3335_);
                        crate::leanh::lean_inc(v_quotContext_3334_);
                        v___y_3196_ = v___y_3319_;
                        v___y_3197_ = v_quotContext_3334_;
                        v___y_3198_ = v___x_3360_;
                        v___y_3199_ = v___x_3371_;
                        v___y_3200_ = v___y_3324_;
                        v___y_3201_ = v___y_3327_;
                        v___y_3202_ = v___x_3352_;
                        v___y_3203_ = v___x_3351_;
                        v___y_3204_ = v___y_3320_;
                        v___y_3205_ = v_a_3342_;
                        v___y_3206_ = v_a_3343_;
                        v___y_3207_ = v___y_3322_;
                        v___y_3208_ = v___x_3345_;
                        v___y_3209_ = v___y_3325_;
                        v___y_3210_ = v___x_3344_;
                        v___y_3211_ = v___x_3367_;
                        v___y_3212_ = v_currMacroScope_3335_;
                        v___y_3213_ = v___x_3369_;
                        v___y_3214_ = v___x_3350_;
                        v___y_3215_ = v_wds_x3f_3330_;
                        v___y_3216_ = v___x_3373_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___y_3318_);
                        v___x_3374_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                        crate::leanh::lean_inc(v_currMacroScope_3335_);
                        crate::leanh::lean_inc(v_quotContext_3334_);
                        v___y_3196_ = v___y_3319_;
                        v___y_3197_ = v_quotContext_3334_;
                        v___y_3198_ = v___x_3360_;
                        v___y_3199_ = v___x_3371_;
                        v___y_3200_ = v___y_3324_;
                        v___y_3201_ = v___y_3327_;
                        v___y_3202_ = v___x_3352_;
                        v___y_3203_ = v___x_3351_;
                        v___y_3204_ = v___y_3320_;
                        v___y_3205_ = v_a_3342_;
                        v___y_3206_ = v_a_3343_;
                        v___y_3207_ = v___y_3322_;
                        v___y_3208_ = v___x_3345_;
                        v___y_3209_ = v___y_3325_;
                        v___y_3210_ = v___x_3344_;
                        v___y_3211_ = v___x_3367_;
                        v___y_3212_ = v_currMacroScope_3335_;
                        v___y_3213_ = v___x_3369_;
                        v___y_3214_ = v___x_3350_;
                        v___y_3215_ = v_wds_x3f_3330_;
                        v___y_3216_ = v___x_3374_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_ref_3339_);
                    crate::leanh::lean_dec(v_wds_x3f_3330_);
                    crate::leanh::lean_dec(v___y_3321_);
                    crate::leanh::lean_dec(v___y_3319_);
                    crate::leanh::lean_dec(v___y_3318_);
                    v_a_3375_ = crate::leanh::lean_ctor_get(v___x_3341_, 0);
                    v_a_3376_ = crate::leanh::lean_ctor_get(v___x_3341_, 1);
                    v_isSharedCheck_3383_ = (!crate::leanh::lean_is_exclusive(v___x_3341_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3378_ = v___x_3341_;
                        v_isShared_3379_ = v_isSharedCheck_3383_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3376_);
                        crate::leanh::lean_inc(v_a_3375_);
                        crate::leanh::lean_dec(v___x_3341_);
                        v___x_3378_ = crate::leanh::lean_box(0);
                        v_isShared_3379_ = v_isSharedCheck_3383_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_3379_ == 0 {
                    v___x_3381_ = v___x_3378_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3382_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3376_);
                    v___x_3381_ = v_reuseFailAlloc_3382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3381_;
            }
            7 => {
                crate::leanh::lean_inc_ref_n(v___y_3397_, 2);
                v___x_3399_ = l_Array_append___redArg(v___y_3397_, v___y_3398_);
                crate::leanh::lean_dec_ref(v___y_3398_);
                crate::leanh::lean_inc_n(v___y_3389_, 2);
                crate::leanh::lean_inc_n(v___y_3385_, 6);
                v___x_3400_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3400_, 0, v___y_3385_);
                crate::leanh::lean_ctor_set(v___x_3400_, 1, v___y_3389_);
                crate::leanh::lean_ctor_set(v___x_3400_, 2, v___x_3399_);
                v___x_3401_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                v___x_3402_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25;
                crate::leanh::lean_inc_ref_n(v___y_3388_, 2);
                crate::leanh::lean_inc_ref_n(v___y_3390_, 2);
                v___x_3403_ =
                    l_Lean_Name_mkStr4(v___y_3390_, v___y_3388_, v___x_3401_, v___x_3402_);
                v___x_3404_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38;
                v___x_3405_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3405_, 0, v___y_3385_);
                crate::leanh::lean_ctor_set(v___x_3405_, 1, v___x_3404_);
                crate::leanh::lean_inc_ref(v___y_3386_);
                v___x_3406_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3406_, 0, v___y_3385_);
                crate::leanh::lean_ctor_set(v___x_3406_, 1, v___y_3386_);
                crate::leanh::lean_inc(v___y_3394_);
                v___x_3407_ =
                    l_Lean_Syntax_node2(v___y_3385_, v___y_3394_, v___x_3406_, v___y_3393_);
                v___x_3408_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26;
                v___x_3409_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27;
                v___x_3410_ =
                    l_Lean_Name_mkStr4(v___y_3390_, v___y_3388_, v___x_3408_, v___x_3409_);
                v___x_3411_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3411_, 0, v___y_3385_);
                crate::leanh::lean_ctor_set(v___x_3411_, 1, v___y_3389_);
                crate::leanh::lean_ctor_set(v___x_3411_, 2, v___y_3397_);
                crate::leanh::lean_inc_ref(v___x_3411_);
                v___x_3412_ =
                    l_Lean_Syntax_node2(v___y_3385_, v___x_3410_, v___x_3411_, v___x_3411_);
                if crate::leanh::lean_obj_tag(v___y_3391_) == 1 {
                    v_val_3413_ = crate::leanh::lean_ctor_get(v___y_3391_, 0);
                    crate::leanh::lean_inc(v_val_3413_);
                    crate::leanh::lean_dec_ref_known(v___y_3391_, 1);
                    v___x_3414_ = l_Array_mkArray1___redArg(v_val_3413_);
                    v___y_3173_ = v___x_3403_;
                    v___y_3174_ = v___x_3407_;
                    v___y_3175_ = v___y_3385_;
                    v___y_3176_ = v___x_3412_;
                    v___y_3177_ = v___x_3405_;
                    v___y_3178_ = v___y_3389_;
                    v___y_3179_ = v___y_3392_;
                    v___y_3180_ = v___y_3387_;
                    v___y_3181_ = v___y_3395_;
                    v___y_3182_ = v___y_3396_;
                    v___y_3183_ = v___x_3400_;
                    v___y_3184_ = v___y_3397_;
                    v___y_3185_ = v___x_3414_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3391_);
                    v___x_3415_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                    v___y_3173_ = v___x_3403_;
                    v___y_3174_ = v___x_3407_;
                    v___y_3175_ = v___y_3385_;
                    v___y_3176_ = v___x_3412_;
                    v___y_3177_ = v___x_3405_;
                    v___y_3178_ = v___y_3389_;
                    v___y_3179_ = v___y_3392_;
                    v___y_3180_ = v___y_3387_;
                    v___y_3181_ = v___y_3395_;
                    v___y_3182_ = v___y_3396_;
                    v___y_3183_ = v___x_3400_;
                    v___y_3184_ = v___y_3397_;
                    v___y_3185_ = v___x_3415_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_3429_);
                v___x_3431_ = l_Array_append___redArg(v___y_3429_, v___y_3430_);
                crate::leanh::lean_dec_ref(v___y_3430_);
                crate::leanh::lean_inc(v___y_3422_);
                crate::leanh::lean_inc(v___y_3417_);
                v___x_3432_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3432_, 0, v___y_3417_);
                crate::leanh::lean_ctor_set(v___x_3432_, 1, v___y_3422_);
                crate::leanh::lean_ctor_set(v___x_3432_, 2, v___x_3431_);
                v___x_3433_ = l_Lean_SourceInfo_fromRef(v___y_3424_, v___x_3191_);
                crate::leanh::lean_dec(v___y_3424_);
                v___x_3434_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23;
                v___x_3435_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3435_, 0, v___x_3433_);
                crate::leanh::lean_ctor_set(v___x_3435_, 1, v___x_3434_);
                if crate::leanh::lean_obj_tag(v___y_3418_) == 1 {
                    v_val_3436_ = crate::leanh::lean_ctor_get(v___y_3418_, 0);
                    crate::leanh::lean_inc(v_val_3436_);
                    crate::leanh::lean_dec_ref_known(v___y_3418_, 1);
                    v___x_3437_ = l_Array_mkArray1___redArg(v_val_3436_);
                    v___y_3385_ = v___y_3417_;
                    v___y_3386_ = v___y_3419_;
                    v___y_3387_ = v___y_3420_;
                    v___y_3388_ = v___y_3421_;
                    v___y_3389_ = v___y_3422_;
                    v___y_3390_ = v___y_3423_;
                    v___y_3391_ = v___y_3425_;
                    v___y_3392_ = v___y_3426_;
                    v___y_3393_ = v___y_3427_;
                    v___y_3394_ = v___y_3428_;
                    v___y_3395_ = v___x_3435_;
                    v___y_3396_ = v___x_3432_;
                    v___y_3397_ = v___y_3429_;
                    v___y_3398_ = v___x_3437_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3418_);
                    v___x_3438_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                    v___y_3385_ = v___y_3417_;
                    v___y_3386_ = v___y_3419_;
                    v___y_3387_ = v___y_3420_;
                    v___y_3388_ = v___y_3421_;
                    v___y_3389_ = v___y_3422_;
                    v___y_3390_ = v___y_3423_;
                    v___y_3391_ = v___y_3425_;
                    v___y_3392_ = v___y_3426_;
                    v___y_3393_ = v___y_3427_;
                    v___y_3394_ = v___y_3428_;
                    v___y_3395_ = v___x_3435_;
                    v___y_3396_ = v___x_3432_;
                    v___y_3397_ = v___y_3429_;
                    v___y_3398_ = v___x_3438_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref(v___y_3452_);
                v___x_3454_ = l_Array_append___redArg(v___y_3452_, v___y_3453_);
                crate::leanh::lean_dec_ref(v___y_3453_);
                crate::leanh::lean_inc(v___y_3445_);
                crate::leanh::lean_inc(v___y_3440_);
                v___x_3455_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3455_, 0, v___y_3440_);
                crate::leanh::lean_ctor_set(v___x_3455_, 1, v___y_3445_);
                crate::leanh::lean_ctor_set(v___x_3455_, 2, v___x_3454_);
                if crate::leanh::lean_obj_tag(v___y_3443_) == 1 {
                    v_val_3456_ = crate::leanh::lean_ctor_get(v___y_3443_, 0);
                    crate::leanh::lean_inc(v_val_3456_);
                    crate::leanh::lean_dec_ref_known(v___y_3443_, 1);
                    v___x_3457_ = l_Array_mkArray1___redArg(v_val_3456_);
                    v___y_3417_ = v___y_3440_;
                    v___y_3418_ = v___y_3441_;
                    v___y_3419_ = v___y_3442_;
                    v___y_3420_ = v___x_3455_;
                    v___y_3421_ = v___y_3444_;
                    v___y_3422_ = v___y_3445_;
                    v___y_3423_ = v___y_3446_;
                    v___y_3424_ = v___y_3447_;
                    v___y_3425_ = v___y_3448_;
                    v___y_3426_ = v___y_3449_;
                    v___y_3427_ = v___y_3450_;
                    v___y_3428_ = v___y_3451_;
                    v___y_3429_ = v___y_3452_;
                    v___y_3430_ = v___x_3457_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3443_);
                    v___x_3458_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                    v___y_3417_ = v___y_3440_;
                    v___y_3418_ = v___y_3441_;
                    v___y_3419_ = v___y_3442_;
                    v___y_3420_ = v___x_3455_;
                    v___y_3421_ = v___y_3444_;
                    v___y_3422_ = v___y_3445_;
                    v___y_3423_ = v___y_3446_;
                    v___y_3424_ = v___y_3447_;
                    v___y_3425_ = v___y_3448_;
                    v___y_3426_ = v___y_3449_;
                    v___y_3427_ = v___y_3450_;
                    v___y_3428_ = v___y_3451_;
                    v___y_3429_ = v___y_3452_;
                    v___y_3430_ = v___x_3458_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v_ref_3472_ = crate::leanh::lean_ctor_get(v___y_3470_, 5);
                v___x_3473_ = 0;
                v___x_3474_ = l_Lean_SourceInfo_fromRef(v_ref_3472_, v___x_3473_);
                v___x_3475_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                v___x_3476_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                if crate::leanh::lean_obj_tag(v___y_3460_) == 1 {
                    v_val_3477_ = crate::leanh::lean_ctor_get(v___y_3460_, 0);
                    crate::leanh::lean_inc(v_val_3477_);
                    crate::leanh::lean_dec_ref_known(v___y_3460_, 1);
                    v___x_3478_ = l_Array_mkArray1___redArg(v_val_3477_);
                    v___y_3440_ = v___x_3474_;
                    v___y_3441_ = v___y_3463_;
                    v___y_3442_ = v___y_3464_;
                    v___y_3443_ = v___y_3461_;
                    v___y_3444_ = v___y_3462_;
                    v___y_3445_ = v___x_3475_;
                    v___y_3446_ = v___y_3465_;
                    v___y_3447_ = v___y_3466_;
                    v___y_3448_ = v_wds_x3f_3469_;
                    v___y_3449_ = v___y_3471_;
                    v___y_3450_ = v___y_3467_;
                    v___y_3451_ = v___y_3468_;
                    v___y_3452_ = v___x_3476_;
                    v___y_3453_ = v___x_3478_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3460_);
                    v___x_3479_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                    v___y_3440_ = v___x_3474_;
                    v___y_3441_ = v___y_3463_;
                    v___y_3442_ = v___y_3464_;
                    v___y_3443_ = v___y_3461_;
                    v___y_3444_ = v___y_3462_;
                    v___y_3445_ = v___x_3475_;
                    v___y_3446_ = v___y_3465_;
                    v___y_3447_ = v___y_3466_;
                    v___y_3448_ = v_wds_x3f_3469_;
                    v___y_3449_ = v___y_3471_;
                    v___y_3450_ = v___y_3467_;
                    v___y_3451_ = v___y_3468_;
                    v___y_3452_ = v___x_3476_;
                    v___y_3453_ = v___x_3479_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                v___x_3490_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_3491_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3490_);
                v___x_3492_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26;
                crate::leanh::lean_inc(v___x_3491_);
                v___x_3493_ = l_Lean_Syntax_isOfKind(v___x_3491_, v___x_3492_);
                if v___x_3493_ == 0 {
                    v___x_3494_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                    v___x_3495_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15;
                    v___x_3496_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                    v___x_3497_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27;
                    crate::leanh::lean_inc(v___x_3491_);
                    v___x_3498_ = l_Lean_Syntax_isOfKind(v___x_3491_, v___x_3497_);
                    if v___x_3498_ == 0 {
                        crate::leanh::lean_dec(v___x_3491_);
                        crate::leanh::lean_dec(v_pkg_x3f_3487_);
                        crate::leanh::lean_dec(v___y_3483_);
                        crate::leanh::lean_dec(v___y_3482_);
                        crate::leanh::lean_dec(v___y_3481_);
                        v___x_3499_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3500_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3499_,
                            v___y_3488_,
                            v___y_3489_,
                        );
                        crate::leanh::lean_dec(v_stx_3145_);
                        return v___x_3500_;
                    } else {
                        v___x_3501_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3485_);
                        v___x_3502_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28;
                        crate::leanh::lean_inc(v___x_3501_);
                        v___x_3503_ = l_Lean_Syntax_isOfKind(v___x_3501_, v___x_3502_);
                        if v___x_3503_ == 0 {
                            crate::leanh::lean_dec(v___x_3501_);
                            crate::leanh::lean_dec(v___x_3491_);
                            crate::leanh::lean_dec(v_pkg_x3f_3487_);
                            crate::leanh::lean_dec(v___y_3483_);
                            crate::leanh::lean_dec(v___y_3482_);
                            crate::leanh::lean_dec(v___y_3481_);
                            v___x_3504_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                            v___x_3505_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_3145_,
                                v___x_3504_,
                                v___y_3488_,
                                v___y_3489_,
                            );
                            crate::leanh::lean_dec(v_stx_3145_);
                            return v___x_3505_;
                        } else {
                            v___x_3506_ = l_Lean_Syntax_getArg(v___x_3501_, v___x_3194_);
                            v___x_3507_ = l_Lean_Syntax_matchesNull(v___x_3506_, v___x_3194_);
                            if v___x_3507_ == 0 {
                                crate::leanh::lean_dec(v___x_3501_);
                                crate::leanh::lean_dec(v___x_3491_);
                                crate::leanh::lean_dec(v_pkg_x3f_3487_);
                                crate::leanh::lean_dec(v___y_3483_);
                                crate::leanh::lean_dec(v___y_3482_);
                                crate::leanh::lean_dec(v___y_3481_);
                                v___x_3508_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                v___x_3509_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3145_,
                                    v___x_3508_,
                                    v___y_3488_,
                                    v___y_3489_,
                                );
                                crate::leanh::lean_dec(v_stx_3145_);
                                return v___x_3509_;
                            } else {
                                v___x_3510_ = l_Lean_Syntax_getArg(v___x_3501_, v___y_3486_);
                                crate::leanh::lean_dec(v___x_3501_);
                                v___x_3511_ = l_Lean_Syntax_matchesNull(v___x_3510_, v___x_3194_);
                                if v___x_3511_ == 0 {
                                    crate::leanh::lean_dec(v___x_3491_);
                                    crate::leanh::lean_dec(v_pkg_x3f_3487_);
                                    crate::leanh::lean_dec(v___y_3483_);
                                    crate::leanh::lean_dec(v___y_3482_);
                                    crate::leanh::lean_dec(v___y_3481_);
                                    v___x_3512_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                    v___x_3513_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_stx_3145_,
                                        v___x_3512_,
                                        v___y_3488_,
                                        v___y_3489_,
                                    );
                                    crate::leanh::lean_dec(v_stx_3145_);
                                    return v___x_3513_;
                                } else {
                                    v___x_3514_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3486_);
                                    v___x_3515_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3484_);
                                    crate::leanh::lean_dec(v___x_3491_);
                                    v___x_3516_ = l_Lean_Syntax_isNone(v___x_3515_);
                                    if v___x_3516_ == 0 {
                                        crate::leanh::lean_inc(v___x_3515_);
                                        v___x_3517_ =
                                            l_Lean_Syntax_matchesNull(v___x_3515_, v___y_3486_);
                                        if v___x_3517_ == 0 {
                                            crate::leanh::lean_dec(v___x_3515_);
                                            crate::leanh::lean_dec(v___x_3514_);
                                            crate::leanh::lean_dec(v_pkg_x3f_3487_);
                                            crate::leanh::lean_dec(v___y_3483_);
                                            crate::leanh::lean_dec(v___y_3482_);
                                            crate::leanh::lean_dec(v___y_3481_);
                                            v___x_3518_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                            v___x_3519_ = l_Lean_Macro_throwErrorAt___redArg(
                                                v_stx_3145_,
                                                v___x_3518_,
                                                v___y_3488_,
                                                v___y_3489_,
                                            );
                                            crate::leanh::lean_dec(v_stx_3145_);
                                            return v___x_3519_;
                                        } else {
                                            v_wds_x3f_3520_ =
                                                l_Lean_Syntax_getArg(v___x_3515_, v___x_3194_);
                                            crate::leanh::lean_dec(v___x_3515_);
                                            v___x_3521_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                            crate::leanh::lean_inc(v_wds_x3f_3520_);
                                            v___x_3522_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_3520_,
                                                v___x_3521_,
                                            );
                                            if v___x_3522_ == 0 {
                                                crate::leanh::lean_dec(v_wds_x3f_3520_);
                                                crate::leanh::lean_dec(v___x_3514_);
                                                crate::leanh::lean_dec(v_pkg_x3f_3487_);
                                                crate::leanh::lean_dec(v___y_3483_);
                                                crate::leanh::lean_dec(v___y_3482_);
                                                crate::leanh::lean_dec(v___y_3481_);
                                                v___x_3523_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                                v___x_3524_ = l_Lean_Macro_throwErrorAt___redArg(
                                                    v_stx_3145_,
                                                    v___x_3523_,
                                                    v___y_3488_,
                                                    v___y_3489_,
                                                );
                                                crate::leanh::lean_dec(v_stx_3145_);
                                                return v___x_3524_;
                                            } else {
                                                crate::leanh::lean_dec(v_stx_3145_);
                                                v___x_3525_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3525_,
                                                    0,
                                                    v_wds_x3f_3520_,
                                                );
                                                v___y_3318_ = v___y_3481_;
                                                v___y_3319_ = v___x_3514_;
                                                v___y_3320_ = v___x_3497_;
                                                v___y_3321_ = v___y_3482_;
                                                v___y_3322_ = v___x_3495_;
                                                v___y_3323_ = v_pkg_x3f_3487_;
                                                v___y_3324_ = v___x_3496_;
                                                v___y_3325_ = v___x_3502_;
                                                v___y_3326_ = v___y_3483_;
                                                v___y_3327_ = v___x_3494_;
                                                v___y_3328_ = v___y_3486_;
                                                v___y_3329_ = v___x_3493_;
                                                v_wds_x3f_3330_ = v___x_3525_;
                                                v___y_3331_ = v___y_3488_;
                                                v___y_3332_ = v___y_3489_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v___x_3515_);
                                        crate::leanh::lean_dec(v_stx_3145_);
                                        v___x_3526_ = crate::leanh::lean_box(0);
                                        v___y_3318_ = v___y_3481_;
                                        v___y_3319_ = v___x_3514_;
                                        v___y_3320_ = v___x_3497_;
                                        v___y_3321_ = v___y_3482_;
                                        v___y_3322_ = v___x_3495_;
                                        v___y_3323_ = v_pkg_x3f_3487_;
                                        v___y_3324_ = v___x_3496_;
                                        v___y_3325_ = v___x_3502_;
                                        v___y_3326_ = v___y_3483_;
                                        v___y_3327_ = v___x_3494_;
                                        v___y_3328_ = v___y_3486_;
                                        v___y_3329_ = v___x_3493_;
                                        v_wds_x3f_3330_ = v___x_3526_;
                                        v___y_3331_ = v___y_3488_;
                                        v___y_3332_ = v___y_3489_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    v___x_3527_ = l_Lean_Syntax_getArg(v___x_3491_, v___x_3194_);
                    v___x_3528_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                    v___x_3529_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15;
                    v___x_3530_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29;
                    v___x_3531_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30;
                    crate::leanh::lean_inc(v___x_3527_);
                    v___x_3532_ = l_Lean_Syntax_isOfKind(v___x_3527_, v___x_3531_);
                    if v___x_3532_ == 0 {
                        crate::leanh::lean_dec(v___x_3527_);
                        crate::leanh::lean_dec(v___x_3491_);
                        crate::leanh::lean_dec(v_pkg_x3f_3487_);
                        crate::leanh::lean_dec(v___y_3483_);
                        crate::leanh::lean_dec(v___y_3482_);
                        crate::leanh::lean_dec(v___y_3481_);
                        v___x_3533_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3534_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3533_,
                            v___y_3488_,
                            v___y_3489_,
                        );
                        crate::leanh::lean_dec(v_stx_3145_);
                        return v___x_3534_;
                    } else {
                        v___x_3535_ = l_Lean_Syntax_getArg(v___x_3527_, v___y_3486_);
                        crate::leanh::lean_dec(v___x_3527_);
                        v___x_3536_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3486_);
                        crate::leanh::lean_dec(v___x_3491_);
                        v___x_3537_ = l_Lean_Syntax_isNone(v___x_3536_);
                        if v___x_3537_ == 0 {
                            crate::leanh::lean_inc(v___x_3536_);
                            v___x_3538_ = l_Lean_Syntax_matchesNull(v___x_3536_, v___y_3486_);
                            if v___x_3538_ == 0 {
                                crate::leanh::lean_dec(v___x_3536_);
                                crate::leanh::lean_dec(v___x_3535_);
                                crate::leanh::lean_dec(v_pkg_x3f_3487_);
                                crate::leanh::lean_dec(v___y_3483_);
                                crate::leanh::lean_dec(v___y_3482_);
                                crate::leanh::lean_dec(v___y_3481_);
                                v___x_3539_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                v___x_3540_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3145_,
                                    v___x_3539_,
                                    v___y_3488_,
                                    v___y_3489_,
                                );
                                crate::leanh::lean_dec(v_stx_3145_);
                                return v___x_3540_;
                            } else {
                                v_wds_x3f_3541_ = l_Lean_Syntax_getArg(v___x_3536_, v___x_3194_);
                                crate::leanh::lean_dec(v___x_3536_);
                                v___x_3542_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                crate::leanh::lean_inc(v_wds_x3f_3541_);
                                v___x_3543_ = l_Lean_Syntax_isOfKind(v_wds_x3f_3541_, v___x_3542_);
                                if v___x_3543_ == 0 {
                                    crate::leanh::lean_dec(v_wds_x3f_3541_);
                                    crate::leanh::lean_dec(v___x_3535_);
                                    crate::leanh::lean_dec(v_pkg_x3f_3487_);
                                    crate::leanh::lean_dec(v___y_3483_);
                                    crate::leanh::lean_dec(v___y_3482_);
                                    crate::leanh::lean_dec(v___y_3481_);
                                    v___x_3544_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                    v___x_3545_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_stx_3145_,
                                        v___x_3544_,
                                        v___y_3488_,
                                        v___y_3489_,
                                    );
                                    crate::leanh::lean_dec(v_stx_3145_);
                                    return v___x_3545_;
                                } else {
                                    crate::leanh::lean_dec(v_stx_3145_);
                                    v___x_3546_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3546_, 0, v_wds_x3f_3541_);
                                    v___y_3460_ = v___y_3481_;
                                    v___y_3461_ = v___y_3482_;
                                    v___y_3462_ = v___x_3529_;
                                    v___y_3463_ = v_pkg_x3f_3487_;
                                    v___y_3464_ = v___x_3530_;
                                    v___y_3465_ = v___x_3528_;
                                    v___y_3466_ = v___y_3483_;
                                    v___y_3467_ = v___x_3535_;
                                    v___y_3468_ = v___x_3531_;
                                    v_wds_x3f_3469_ = v___x_3546_;
                                    v___y_3470_ = v___y_3488_;
                                    v___y_3471_ = v___y_3489_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_3536_);
                            crate::leanh::lean_dec(v_stx_3145_);
                            v___x_3547_ = crate::leanh::lean_box(0);
                            v___y_3460_ = v___y_3481_;
                            v___y_3461_ = v___y_3482_;
                            v___y_3462_ = v___x_3529_;
                            v___y_3463_ = v_pkg_x3f_3487_;
                            v___y_3464_ = v___x_3530_;
                            v___y_3465_ = v___x_3528_;
                            v___y_3466_ = v___y_3483_;
                            v___y_3467_ = v___x_3535_;
                            v___y_3468_ = v___x_3531_;
                            v_wds_x3f_3469_ = v___x_3547_;
                            v___y_3470_ = v___y_3488_;
                            v___y_3471_ = v___y_3489_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_3554_ = crate::leanh::lean_unsigned_to_nat(2);
                v_kw_3555_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3554_);
                v___x_3556_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_3557_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3556_);
                v___x_3558_ = l_Lean_Syntax_isNone(v___x_3557_);
                if v___x_3558_ == 0 {
                    crate::leanh::lean_inc(v___x_3557_);
                    v___x_3559_ = l_Lean_Syntax_matchesNull(v___x_3557_, v___y_3550_);
                    if v___x_3559_ == 0 {
                        crate::leanh::lean_dec(v___x_3557_);
                        crate::leanh::lean_dec(v_kw_3555_);
                        crate::leanh::lean_dec(v_attrs_x3f_3551_);
                        crate::leanh::lean_dec(v___y_3549_);
                        v___x_3560_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3561_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3560_,
                            v___y_3552_,
                            v___y_3553_,
                        );
                        crate::leanh::lean_dec(v_stx_3145_);
                        return v___x_3561_;
                    } else {
                        v_pkg_x3f_3562_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_3194_);
                        crate::leanh::lean_dec(v___x_3557_);
                        v___x_3563_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3563_, 0, v_pkg_x3f_3562_);
                        v___y_3481_ = v___y_3549_;
                        v___y_3482_ = v_attrs_x3f_3551_;
                        v___y_3483_ = v_kw_3555_;
                        v___y_3484_ = v___x_3556_;
                        v___y_3485_ = v___x_3554_;
                        v___y_3486_ = v___y_3550_;
                        v_pkg_x3f_3487_ = v___x_3563_;
                        v___y_3488_ = v___y_3552_;
                        v___y_3489_ = v___y_3553_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3557_);
                    v___x_3564_ = crate::leanh::lean_box(0);
                    v___y_3481_ = v___y_3549_;
                    v___y_3482_ = v_attrs_x3f_3551_;
                    v___y_3483_ = v_kw_3555_;
                    v___y_3484_ = v___x_3556_;
                    v___y_3485_ = v___x_3554_;
                    v___y_3486_ = v___y_3550_;
                    v_pkg_x3f_3487_ = v___x_3564_;
                    v___y_3488_ = v___y_3552_;
                    v___y_3489_ = v___y_3553_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                v___x_3569_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3570_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3569_);
                v___x_3571_ = l_Lean_Syntax_isNone(v___x_3570_);
                if v___x_3571_ == 0 {
                    crate::leanh::lean_inc(v___x_3570_);
                    v___x_3572_ = l_Lean_Syntax_matchesNull(v___x_3570_, v___x_3569_);
                    if v___x_3572_ == 0 {
                        crate::leanh::lean_dec(v___x_3570_);
                        crate::leanh::lean_dec(v_doc_x3f_3566_);
                        v___x_3573_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3574_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3573_,
                            v___y_3567_,
                            v___y_3568_,
                        );
                        crate::leanh::lean_dec(v_stx_3145_);
                        return v___x_3574_;
                    } else {
                        v_attrs_x3f_3575_ = l_Lean_Syntax_getArg(v___x_3570_, v___x_3194_);
                        crate::leanh::lean_dec(v___x_3570_);
                        v___x_3576_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3576_, 0, v_attrs_x3f_3575_);
                        v___y_3549_ = v_doc_x3f_3566_;
                        v___y_3550_ = v___x_3569_;
                        v_attrs_x3f_3551_ = v___x_3576_;
                        v___y_3552_ = v___y_3567_;
                        v___y_3553_ = v___y_3568_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3570_);
                    v___x_3577_ = crate::leanh::lean_box(0);
                    v___y_3549_ = v_doc_x3f_3566_;
                    v___y_3550_ = v___x_3569_;
                    v_attrs_x3f_3551_ = v___x_3577_;
                    v___y_3552_ = v___y_3567_;
                    v___y_3553_ = v___y_3568_;
                    state = 12;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed(
    mut v_stx_3587_: *mut crate::leanh::LeanObject,
    mut v_a_3588_: *mut crate::leanh::LeanObject,
    mut v_a_3589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3590_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(
        v_stx_3587_,
        v_a_3588_,
        v_a_3589_,
    );
    crate::leanh::lean_dec_ref(v_a_3588_);
    return v_res_3590_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_Lean_Elab_macroAttribute;
    v___x_3597_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1;
    v___x_3598_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1;
    v___x_3599_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___boxed
            as *mut core::ffi::c_void,
        3,
        0,
    );
    v___x_3600_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3596_,
        v___x_3597_,
        v___x_3598_,
        v___x_3599_,
    );
    return v___x_3600_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___boxed(
    mut v_a_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3602_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
    return v_res_3602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Package(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lake_DSL_Extensions(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Package(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_DSL_Package(builtin);
}
