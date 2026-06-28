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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 77, 111, 100, 105, 102, 105, 101, 114, 115, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__2_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3_value) as *mut LeanObject;
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__5_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [100, 101, 102, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 108, 73, 100, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [111, 112, 116, 68, 101, 99, 108, 83, 105, 103, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 121, 112, 101, 83, 112, 101, 99, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [119, 104, 101, 114, 101, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 101, 114, 101, 83, 116, 114, 117, 99, 116, 73, 110, 115, 116, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__17_value) as *mut LeanObject,7794500365561932708 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 97, 107, 101, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 83, 76, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [111, 112, 116, 67, 111, 110, 102, 105, 103, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__21_value) as *mut LeanObject,2937396280676515247 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [105, 108, 108, 45, 102, 111, 114, 109, 101, 100, 32, 99, 111, 110, 102, 105, 103, 117, 114, 97, 116, 105, 111, 110, 32, 115, 121, 110, 116, 97, 120, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23_value) as *mut LeanObject;
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [100, 101, 99, 108, 86, 97, 108, 87, 104, 101, 114, 101, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__25_value) as *mut LeanObject,5906021167542994327 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [100, 101, 99, 108, 86, 97, 108, 83, 116, 114, 117, 99, 116, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__27_value) as *mut LeanObject,1004026287653508741 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [115, 116, 114, 117, 99, 116, 86, 97, 108, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__29_value) as *mut LeanObject,10845500395294116975 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 116, 114, 117, 99, 116, 73, 110, 115, 116, 70, 105, 101, 108, 100, 115, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__31_value) as *mut LeanObject,5018042693327868416 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32_value) as *mut LeanObject;
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [119, 104, 101, 114, 101, 68, 101, 99, 108, 115, 0]};
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value) as *mut LeanObject;
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__33_value) as *mut LeanObject,4503069825835506739 as *mut LeanObject] };
static mut l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34: *mut LeanObject = core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__1_value
        ) as *mut LeanObject,
        9232979286016572671 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__8_value
        ) as *mut LeanObject,
        12277407653222002017 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__11_value
        ) as *mut LeanObject,
        3605886163266385533 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__18_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value
        ) as *mut LeanObject,
        9855517672881652961 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19_value
        ) as *mut LeanObject,
        14292882441629431293 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__22_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__32_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__33_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34_value
        ) as *mut LeanObject,
        13060808746942009198 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40_value
        ) as *mut LeanObject,
        5783777625530456636 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43_value
        ) as *mut LeanObject,
        1448088012876701721 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46_value
        ) as *mut LeanObject,
        14398486047628956367 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__49_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__50_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value:
    LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__55_value
        ) as *mut LeanObject,
        6671755061125946191 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__59_value
        ) as *mut LeanObject,
        13306843946249674491 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__60_value
        ) as *mut LeanObject,
        7229350633979142691 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value:
    LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__62_value
        ) as *mut LeanObject,
        15699985925601833486 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__64_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65_value
        ) as *mut LeanObject,
        5998648494902257236 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__0_value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,12997130533650095963 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,11286550318989764116 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [80, 97, 99, 107, 97, 103, 101, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__4_value) as *mut LeanObject,15681734397375188879 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__5_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,16086747790069339938 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__6_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,11922365661391839154 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,17745535245540040497 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 80, 97, 99, 107, 97, 103, 101, 67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__9_value) as *mut LeanObject,17339603636372616795 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__0_value
        ) as *mut LeanObject,
        7248721378401769890 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value:
    LeanStringObject<35> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value:
    LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3_value
        ) as *mut LeanObject,
        14712175129652721653 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value:
    LeanStringObject<19> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value
        ) as *mut LeanObject,
        5750662100507400969 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6_value
        ) as *mut LeanObject,
        1387310164323292101 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value
        ) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [core::ptr::addr_of!(
        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__9_value
    ) as *mut LeanObject],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12_value
        ) as *mut LeanObject,
        16251518922638631496 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15_value
        ) as *mut LeanObject,
        1077391322905290683 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value:
    LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21_value
) as *mut LeanObject;
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value:
    LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23_value
        ) as *mut LeanObject,
        985716791886485019 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value:
    LeanStringObject<10> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__19_value) as *mut LeanObject,13012506173997729135 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__20_value) as *mut LeanObject,5901868804703194544 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__25_value
        ) as *mut LeanObject,
        11022427548561232637 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16_value) as *mut LeanObject,17342580262104060118 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25_value
        ) as *mut LeanObject,
        13585030837571646948 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26_value
        ) as *mut LeanObject,
        7625897890118033792 as *mut LeanObject,
    ],
};
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27_value
        ) as *mut LeanObject,
        8715860392475343861 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value
) as *mut LeanObject;
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__29_value
        ) as *mut LeanObject,
        5817315006727311029 as *mut LeanObject,
    ],
};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30:
    *mut LeanObject = core::ptr::addr_of!(
    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__30_value
) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [101, 120, 112, 97, 110, 100, 80, 111, 115, 116, 85, 112, 100, 97, 116, 101, 68, 101, 99, 108, 0]};
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__8_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__0_value) as *mut LeanObject,6329611640435385135 as *mut LeanObject] };
static mut l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(
    mut v___y_1802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    v___x_1804_ = lean_st_ref_get(v___y_1802_);
    v_env_1805_ = lean_ctor_get(v___x_1804_, 0);
    lean_inc_ref(v_env_1805_);
    lean_dec(v___x_1804_);
    v___x_1806_ = l_Lean_Environment_header(v_env_1805_);
    lean_dec_ref(v_env_1805_);
    v_mainModule_1807_ = lean_ctor_get(v___x_1806_, 0);
    lean_inc(v_mainModule_1807_);
    lean_dec_ref(v___x_1806_);
    v___x_1808_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1808_, 0, v_mainModule_1807_);
    return v___x_1808_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg___boxed(
    mut v___y_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1811_: *mut LeanObject = core::ptr::null_mut();
    v_res_1811_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1809_);
    lean_dec(v___y_1809_);
    return v_res_1811_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(
    mut v___y_1812_: *mut LeanObject,
    mut v___y_1813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    v___x_1815_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_1813_);
    return v___x_1815_;
}
pub unsafe fn l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___boxed(
    mut v___y_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1819_: *mut LeanObject = core::ptr::null_mut();
    v_res_1819_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2(v___y_1816_, v___y_1817_);
    lean_dec(v___y_1817_);
    lean_dec_ref(v___y_1816_);
    return v_res_1819_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
    mut v___y_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: u8 = 0;
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1833_: u8 = 0;
    let mut v_a_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1837_: u8 = 0;
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1841_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1823_ = l_Lean_Elab_Command_getRef___redArg(v___y_1820_);
                if lean_obj_tag(v___x_1823_) == 0 {
                    v_a_1824_ = lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1833_ = (!lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1833_ == 0 {
                        v___x_1826_ = v___x_1823_;
                        v_isShared_1827_ = v_isSharedCheck_1833_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1824_);
                        lean_dec(v___x_1823_);
                        v___x_1826_ = lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1833_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1834_ = lean_ctor_get(v___x_1823_, 0);
                    v_isSharedCheck_1841_ = (!lean_is_exclusive(v___x_1823_)) as u8;
                    if v_isSharedCheck_1841_ == 0 {
                        v___x_1836_ = v___x_1823_;
                        v_isShared_1837_ = v_isSharedCheck_1841_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1834_);
                        lean_dec(v___x_1823_);
                        v___x_1836_ = lean_box(0);
                        v_isShared_1837_ = v_isSharedCheck_1841_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1828_ = 0;
                v___x_1829_ = l_Lean_SourceInfo_fromRef(v_a_1824_, v___x_1828_);
                lean_dec(v_a_1824_);
                if v_isShared_1827_ == 0 {
                    lean_ctor_set(v___x_1826_, 0, v___x_1829_);
                    v___x_1831_ = v___x_1826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1829_);
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
                    v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
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
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1845_: *mut LeanObject = core::ptr::null_mut();
    v_res_1845_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
        v___y_1842_,
        v___y_1843_,
    );
    lean_dec(v___y_1843_);
    lean_dec_ref(v___y_1842_);
    return v_res_1845_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1846_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1847_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_1848_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1848_, 0, v___x_1847_);
    return v___x_1848_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1849_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_1850_ = lean_unsigned_to_nat(0);
    v___x_1851_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1851_, 0, v___x_1850_);
    lean_ctor_set(v___x_1851_, 1, v___x_1850_);
    lean_ctor_set(v___x_1851_, 2, v___x_1850_);
    lean_ctor_set(v___x_1851_, 3, v___x_1850_);
    lean_ctor_set(v___x_1851_, 4, v___x_1849_);
    lean_ctor_set(v___x_1851_, 5, v___x_1849_);
    lean_ctor_set(v___x_1851_, 6, v___x_1849_);
    lean_ctor_set(v___x_1851_, 7, v___x_1849_);
    lean_ctor_set(v___x_1851_, 8, v___x_1849_);
    lean_ctor_set(v___x_1851_, 9, v___x_1849_);
    return v___x_1851_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    v___x_1852_ = lean_unsigned_to_nat(32);
    v___x_1853_ = lean_mk_empty_array_with_capacity(v___x_1852_);
    v___x_1854_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1854_, 0, v___x_1853_);
    return v___x_1854_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    v___x_1855_ = 5usize;
    v___x_1856_ = lean_unsigned_to_nat(0);
    v___x_1857_ = lean_unsigned_to_nat(32);
    v___x_1858_ = lean_mk_empty_array_with_capacity(v___x_1857_);
    v___x_1859_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_1860_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1860_, 0, v___x_1859_);
    lean_ctor_set(v___x_1860_, 1, v___x_1858_);
    lean_ctor_set(v___x_1860_, 2, v___x_1856_);
    lean_ctor_set(v___x_1860_, 3, v___x_1856_);
    lean_ctor_set_usize(v___x_1860_, 4, v___x_1855_);
    return v___x_1860_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1861_ = lean_box(1);
    v___x_1862_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__4);
    v___x_1863_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_1864_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1864_, 0, v___x_1863_);
    lean_ctor_set(v___x_1864_, 1, v___x_1862_);
    lean_ctor_set(v___x_1864_, 2, v___x_1861_);
    return v___x_1864_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(
    mut v_msgData_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    v___x_1868_ = lean_st_ref_get(v___y_1866_);
    v_env_1869_ = lean_ctor_get(v___x_1868_, 0);
    lean_inc_ref(v_env_1869_);
    lean_dec(v___x_1868_);
    v___x_1870_ = lean_st_ref_get(v___y_1866_);
    v_scopes_1871_ = lean_ctor_get(v___x_1870_, 2);
    lean_inc(v_scopes_1871_);
    lean_dec(v___x_1870_);
    v___x_1872_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1873_ = l_List_head_x21___redArg(v___x_1872_, v_scopes_1871_);
    lean_dec(v_scopes_1871_);
    v_opts_1874_ = lean_ctor_get(v___x_1873_, 1);
    lean_inc_ref(v_opts_1874_);
    lean_dec(v___x_1873_);
    v___x_1875_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__2);
    v___x_1876_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___closed__5);
    v___x_1877_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1877_, 0, v_env_1869_);
    lean_ctor_set(v___x_1877_, 1, v___x_1875_);
    lean_ctor_set(v___x_1877_, 2, v___x_1876_);
    lean_ctor_set(v___x_1877_, 3, v_opts_1874_);
    v___x_1878_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1878_, 0, v___x_1877_);
    lean_ctor_set(v___x_1878_, 1, v_msgData_1865_);
    v___x_1879_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1879_, 0, v___x_1878_);
    return v___x_1879_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_msgData_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
    mut v___y_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1883_: *mut LeanObject = core::ptr::null_mut();
    v_res_1883_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_1880_, v___y_1881_);
    lean_dec(v___y_1881_);
    return v_res_1883_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0()
-> *mut LeanObject {
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    v___x_1884_ = lean_box(1);
    v___x_1885_ = l_Lean_MessageData_ofFormat(v___x_1884_);
    return v___x_1885_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3()
-> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    v___x_1889_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__2;
    v___x_1890_ = l_Lean_MessageData_ofFormat(v___x_1889_);
    return v___x_1890_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(
    mut v_x_1891_: *mut LeanObject,
    mut v_x_1892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v_before_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1901_: u8 = 0;
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1914_: u8 = 0;
    let mut v_unused_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1892_) == 0 {
                    return v_x_1891_;
                } else {
                    v_head_1893_ = lean_ctor_get(v_x_1892_, 0);
                    v_tail_1894_ = lean_ctor_get(v_x_1892_, 1);
                    v_isSharedCheck_1916_ = (!lean_is_exclusive(v_x_1892_)) as u8;
                    if v_isSharedCheck_1916_ == 0 {
                        v___x_1896_ = v_x_1892_;
                        v_isShared_1897_ = v_isSharedCheck_1916_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1894_);
                        lean_inc(v_head_1893_);
                        lean_dec(v_x_1892_);
                        v___x_1896_ = lean_box(0);
                        v_isShared_1897_ = v_isSharedCheck_1916_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1898_ = lean_ctor_get(v_head_1893_, 0);
                v_isSharedCheck_1914_ = (!lean_is_exclusive(v_head_1893_)) as u8;
                if v_isSharedCheck_1914_ == 0 {
                    v_unused_1915_ = lean_ctor_get(v_head_1893_, 1);
                    lean_dec(v_unused_1915_);
                    v___x_1900_ = v_head_1893_;
                    v_isShared_1901_ = v_isSharedCheck_1914_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_1898_);
                    lean_dec(v_head_1893_);
                    v___x_1900_ = lean_box(0);
                    v_isShared_1901_ = v_isSharedCheck_1914_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1902_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
                if v_isShared_1901_ == 0 {
                    lean_ctor_set_tag(v___x_1900_, 7);
                    lean_ctor_set(v___x_1900_, 1, v___x_1902_);
                    lean_ctor_set(v___x_1900_, 0, v_x_1891_);
                    v___x_1904_ = v___x_1900_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1913_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 0, v_x_1891_);
                    lean_ctor_set(v_reuseFailAlloc_1913_, 1, v___x_1902_);
                    v___x_1904_ = v_reuseFailAlloc_1913_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1905_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__3);
                if v_isShared_1897_ == 0 {
                    lean_ctor_set_tag(v___x_1896_, 7);
                    lean_ctor_set(v___x_1896_, 1, v___x_1905_);
                    lean_ctor_set(v___x_1896_, 0, v___x_1904_);
                    v___x_1907_ = v___x_1896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1912_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1904_);
                    lean_ctor_set(v_reuseFailAlloc_1912_, 1, v___x_1905_);
                    v___x_1907_ = v_reuseFailAlloc_1912_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1908_ = l_Lean_MessageData_ofSyntax(v_before_1898_);
                v___x_1909_ = l_Lean_indentD(v___x_1908_);
                v___x_1910_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1910_, 0, v___x_1907_);
                lean_ctor_set(v___x_1910_, 1, v___x_1909_);
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
    mut v_opts_1917_: *mut LeanObject,
    mut v_opt_1918_: *mut LeanObject,
) -> u8 {
    let mut v_name_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    v_name_1919_ = lean_ctor_get(v_opt_1918_, 0);
    v_defValue_1920_ = lean_ctor_get(v_opt_1918_, 1);
    v_map_1921_ = lean_ctor_get(v_opts_1917_, 0);
    v___x_1922_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1921_,
            v_name_1919_,
        );
    if lean_obj_tag(v___x_1922_) == 0 {
        let mut v___x_1923_: u8 = 0;
        v___x_1923_ = (lean_unbox(v_defValue_1920_) as u8);
        return v___x_1923_;
    } else {
        let mut v_val_1924_: *mut LeanObject = core::ptr::null_mut();
        v_val_1924_ = lean_ctor_get(v___x_1922_, 0);
        lean_inc(v_val_1924_);
        lean_dec_ref_known(v___x_1922_, 1);
        if lean_obj_tag(v_val_1924_) == 1 {
            let mut v_v_1925_: u8 = 0;
            v_v_1925_ = lean_ctor_get_uint8(v_val_1924_, 0 as u32);
            lean_dec_ref_known(v_val_1924_, 0);
            return v_v_1925_;
        } else {
            let mut v___x_1926_: u8 = 0;
            lean_dec(v_val_1924_);
            v___x_1926_ = (lean_unbox(v_defValue_1920_) as u8);
            return v___x_1926_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5___boxed(
    mut v_opts_1927_: *mut LeanObject,
    mut v_opt_1928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1929_: u8 = 0;
    let mut v_r_1930_: *mut LeanObject = core::ptr::null_mut();
    v_res_1929_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_1927_, v_opt_1928_);
    lean_dec_ref(v_opt_1928_);
    lean_dec_ref(v_opts_1927_);
    v_r_1930_ = lean_box((v_res_1929_) as usize);
    return v_r_1930_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__1;
    v___x_1935_ = l_Lean_MessageData_ofFormat(v___x_1934_);
    return v___x_1935_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(
    mut v_msgData_1936_: *mut LeanObject,
    mut v_macroStack_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1965_: u8 = 0;
    let mut v_unused_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1940_ = lean_st_ref_get(v___y_1938_);
                v_scopes_1941_ = lean_ctor_get(v___x_1940_, 2);
                lean_inc(v_scopes_1941_);
                lean_dec(v___x_1940_);
                v___x_1942_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1943_ = l_List_head_x21___redArg(v___x_1942_, v_scopes_1941_);
                lean_dec(v_scopes_1941_);
                v_opts_1944_ = lean_ctor_get(v___x_1943_, 1);
                lean_inc_ref(v_opts_1944_);
                lean_dec(v___x_1943_);
                v___x_1945_ = l_Lean_Elab_pp_macroStack;
                v___x_1946_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__5(v_opts_1944_, v___x_1945_);
                lean_dec_ref(v_opts_1944_);
                if v___x_1946_ == 0 {
                    lean_dec(v_macroStack_1937_);
                    v___x_1947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1947_, 0, v_msgData_1936_);
                    return v___x_1947_;
                } else {
                    if lean_obj_tag(v_macroStack_1937_) == 0 {
                        v___x_1948_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1948_, 0, v_msgData_1936_);
                        return v___x_1948_;
                    } else {
                        v_head_1949_ = lean_ctor_get(v_macroStack_1937_, 0);
                        lean_inc(v_head_1949_);
                        v_after_1950_ = lean_ctor_get(v_head_1949_, 1);
                        v_isSharedCheck_1965_ = (!lean_is_exclusive(v_head_1949_)) as u8;
                        if v_isSharedCheck_1965_ == 0 {
                            v_unused_1966_ = lean_ctor_get(v_head_1949_, 0);
                            lean_dec(v_unused_1966_);
                            v___x_1952_ = v_head_1949_;
                            v_isShared_1953_ = v_isSharedCheck_1965_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_1950_);
                            lean_dec(v_head_1949_);
                            v___x_1952_ = lean_box(0);
                            v_isShared_1953_ = v_isSharedCheck_1965_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1954_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6___closed__0);
                if v_isShared_1953_ == 0 {
                    lean_ctor_set_tag(v___x_1952_, 7);
                    lean_ctor_set(v___x_1952_, 1, v___x_1954_);
                    lean_ctor_set(v___x_1952_, 0, v_msgData_1936_);
                    v___x_1956_ = v___x_1952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 0, v_msgData_1936_);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1954_);
                    v___x_1956_ = v_reuseFailAlloc_1964_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1957_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___closed__2);
                v___x_1958_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1958_, 0, v___x_1956_);
                lean_ctor_set(v___x_1958_, 1, v___x_1957_);
                v___x_1959_ = l_Lean_MessageData_ofSyntax(v_after_1950_);
                v___x_1960_ = l_Lean_indentD(v___x_1959_);
                v_msgData_1961_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_1961_, 0, v___x_1958_);
                lean_ctor_set(v_msgData_1961_, 1, v___x_1960_);
                v___x_1962_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3_spec__6(v_msgData_1961_, v_macroStack_1937_);
                v___x_1963_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1963_, 0, v___x_1962_);
                return v___x_1963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg___boxed(
    mut v_msgData_1967_: *mut LeanObject,
    mut v_macroStack_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1971_: *mut LeanObject = core::ptr::null_mut();
    v_res_1971_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_1967_, v_macroStack_1968_, v___y_1969_);
    lean_dec(v___y_1969_);
    return v_res_1971_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(
    mut v_msg_1972_: *mut LeanObject,
    mut v___y_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1986_: u8 = 0;
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1991_: u8 = 0;
    let mut v_a_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1999_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1976_ = l_Lean_Elab_Command_getRef___redArg(v___y_1973_);
                if lean_obj_tag(v___x_1976_) == 0 {
                    v_a_1977_ = lean_ctor_get(v___x_1976_, 0);
                    lean_inc(v_a_1977_);
                    lean_dec_ref_known(v___x_1976_, 1);
                    v_macroStack_1978_ = lean_ctor_get(v___y_1973_, 4);
                    v___x_1979_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msg_1972_, v___y_1974_);
                    v_a_1980_ = lean_ctor_get(v___x_1979_, 0);
                    lean_inc(v_a_1980_);
                    lean_dec_ref(v___x_1979_);
                    v___x_1981_ = l_Lean_Elab_getBetterRef(v_a_1977_, v_macroStack_1978_);
                    lean_dec(v_a_1977_);
                    lean_inc(v_macroStack_1978_);
                    v___x_1982_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_a_1980_, v_macroStack_1978_, v___y_1974_);
                    v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
                    v_isSharedCheck_1991_ = (!lean_is_exclusive(v___x_1982_)) as u8;
                    if v_isSharedCheck_1991_ == 0 {
                        v___x_1985_ = v___x_1982_;
                        v_isShared_1986_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1983_);
                        lean_dec(v___x_1982_);
                        v___x_1985_ = lean_box(0);
                        v_isShared_1986_ = v_isSharedCheck_1991_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_1972_);
                    v_a_1992_ = lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_1999_ = (!lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_1999_ == 0 {
                        v___x_1994_ = v___x_1976_;
                        v_isShared_1995_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1992_);
                        lean_dec(v___x_1976_);
                        v___x_1994_ = lean_box(0);
                        v_isShared_1995_ = v_isSharedCheck_1999_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1987_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1987_, 0, v___x_1981_);
                lean_ctor_set(v___x_1987_, 1, v_a_1983_);
                if v_isShared_1986_ == 0 {
                    lean_ctor_set_tag(v___x_1985_, 1);
                    lean_ctor_set(v___x_1985_, 0, v___x_1987_);
                    v___x_1989_ = v___x_1985_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
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
                    v_reuseFailAlloc_1998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1998_, 0, v_a_1992_);
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
    mut v_msg_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2004_: *mut LeanObject = core::ptr::null_mut();
    v_res_2004_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_2000_, v___y_2001_, v___y_2002_);
    lean_dec(v___y_2002_);
    lean_dec_ref(v___y_2001_);
    return v_res_2004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(
    mut v_ref_2005_: *mut LeanObject,
    mut v_msg_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2021_: u8 = 0;
    let mut v_ref_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2028_: u8 = 0;
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2032_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2010_ = l_Lean_Elab_Command_getRef___redArg(v___y_2007_);
                if lean_obj_tag(v___x_2010_) == 0 {
                    v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
                    lean_inc(v_a_2011_);
                    lean_dec_ref_known(v___x_2010_, 1);
                    v_fileName_2012_ = lean_ctor_get(v___y_2007_, 0);
                    v_fileMap_2013_ = lean_ctor_get(v___y_2007_, 1);
                    v_currRecDepth_2014_ = lean_ctor_get(v___y_2007_, 2);
                    v_cmdPos_2015_ = lean_ctor_get(v___y_2007_, 3);
                    v_macroStack_2016_ = lean_ctor_get(v___y_2007_, 4);
                    v_quotContext_x3f_2017_ = lean_ctor_get(v___y_2007_, 5);
                    v_currMacroScope_2018_ = lean_ctor_get(v___y_2007_, 6);
                    v_snap_x3f_2019_ = lean_ctor_get(v___y_2007_, 8);
                    v_cancelTk_x3f_2020_ = lean_ctor_get(v___y_2007_, 9);
                    v_suppressElabErrors_2021_ = lean_ctor_get_uint8(
                        v___y_2007_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_2022_ = l_Lean_replaceRef(v_ref_2005_, v_a_2011_);
                    lean_dec(v_a_2011_);
                    lean_inc(v_cancelTk_x3f_2020_);
                    lean_inc(v_snap_x3f_2019_);
                    lean_inc(v_currMacroScope_2018_);
                    lean_inc(v_quotContext_x3f_2017_);
                    lean_inc(v_macroStack_2016_);
                    lean_inc(v_cmdPos_2015_);
                    lean_inc(v_currRecDepth_2014_);
                    lean_inc_ref(v_fileMap_2013_);
                    lean_inc_ref(v_fileName_2012_);
                    v___x_2023_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_2023_, 0, v_fileName_2012_);
                    lean_ctor_set(v___x_2023_, 1, v_fileMap_2013_);
                    lean_ctor_set(v___x_2023_, 2, v_currRecDepth_2014_);
                    lean_ctor_set(v___x_2023_, 3, v_cmdPos_2015_);
                    lean_ctor_set(v___x_2023_, 4, v_macroStack_2016_);
                    lean_ctor_set(v___x_2023_, 5, v_quotContext_x3f_2017_);
                    lean_ctor_set(v___x_2023_, 6, v_currMacroScope_2018_);
                    lean_ctor_set(v___x_2023_, 7, v_ref_2022_);
                    lean_ctor_set(v___x_2023_, 8, v_snap_x3f_2019_);
                    lean_ctor_set(v___x_2023_, 9, v_cancelTk_x3f_2020_);
                    lean_ctor_set_uint8(
                        v___x_2023_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2021_,
                    );
                    v___x_2024_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_2006_, v___x_2023_, v___y_2008_);
                    lean_dec_ref_known(v___x_2023_, 10);
                    return v___x_2024_;
                } else {
                    lean_dec_ref(v_msg_2006_);
                    v_a_2025_ = lean_ctor_get(v___x_2010_, 0);
                    v_isSharedCheck_2032_ = (!lean_is_exclusive(v___x_2010_)) as u8;
                    if v_isSharedCheck_2032_ == 0 {
                        v___x_2027_ = v___x_2010_;
                        v_isShared_2028_ = v_isSharedCheck_2032_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2025_);
                        lean_dec(v___x_2010_);
                        v___x_2027_ = lean_box(0);
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
                    v_reuseFailAlloc_2031_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_a_2025_);
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
    mut v_ref_2033_: *mut LeanObject,
    mut v_msg_2034_: *mut LeanObject,
    mut v___y_2035_: *mut LeanObject,
    mut v___y_2036_: *mut LeanObject,
    mut v___y_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2038_: *mut LeanObject = core::ptr::null_mut();
    v_res_2038_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_2033_, v_msg_2034_, v___y_2035_, v___y_2036_);
    lean_dec(v___y_2036_);
    lean_dec_ref(v___y_2035_);
    lean_dec(v_ref_2033_);
    return v_res_2038_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4()
-> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = l_Array_mkArray0(lean_box(0));
    return v___x_2044_;
}
pub unsafe fn _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24()
-> *mut LeanObject {
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    v___x_2072_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__23;
    v___x_2073_ = l_Lean_stringToMessageData(v___x_2072_);
    return v___x_2073_;
}
pub unsafe fn l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(
    mut v_tyName_2101_: *mut LeanObject,
    mut v_id_2102_: *mut LeanObject,
    mut v_ty_2103_: *mut LeanObject,
    mut v_config_2104_: *mut LeanObject,
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2184_: u8 = 0;
    let mut v_a_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2188_: u8 = 0;
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2192_: u8 = 0;
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_whereInfo_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fs_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldMap_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_whereTk_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2217_: u8 = 0;
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2221_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: u8 = 0;
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: u8 = 0;
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: u8 = 0;
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: u8 = 0;
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: u8 = 0;
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fs_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: u8 = 0;
    let mut v___x_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: u8 = 0;
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: u8 = 0;
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fs_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2193_ = l_Lake_PackageConfig_instConfigInfo;
                v___x_2226_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__22;
                lean_inc(v_config_2104_);
                v___x_2227_ = l_Lean_Syntax_isOfKind(v_config_2104_, v___x_2226_);
                if v___x_2227_ == 0 {
                    lean_dec(v_ty_2103_);
                    lean_dec(v_id_2102_);
                    lean_dec(v_tyName_2101_);
                    v___x_2228_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                    v___x_2229_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2228_, v_a_2105_, v_a_2106_);
                    lean_dec(v_config_2104_);
                    return v___x_2229_;
                } else {
                    v___x_2230_ = lean_unsigned_to_nat(0);
                    v___x_2231_ = l_Lean_Syntax_getArg(v_config_2104_, v___x_2230_);
                    lean_inc(v___x_2231_);
                    v___x_2232_ = l_Lean_Syntax_matchesNull(v___x_2231_, v___x_2230_);
                    if v___x_2232_ == 0 {
                        v___x_2233_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_2231_);
                        v___x_2234_ = l_Lean_Syntax_matchesNull(v___x_2231_, v___x_2233_);
                        if v___x_2234_ == 0 {
                            lean_dec(v___x_2231_);
                            lean_dec(v_ty_2103_);
                            lean_dec(v_id_2102_);
                            lean_dec(v_tyName_2101_);
                            v___x_2235_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                            v___x_2236_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2235_, v_a_2105_, v_a_2106_);
                            lean_dec(v_config_2104_);
                            return v___x_2236_;
                        } else {
                            v___x_2237_ = l_Lean_Syntax_getArg(v___x_2231_, v___x_2230_);
                            lean_dec(v___x_2231_);
                            v___x_2238_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__26;
                            lean_inc(v___x_2237_);
                            v___x_2239_ = l_Lean_Syntax_isOfKind(v___x_2237_, v___x_2238_);
                            if v___x_2239_ == 0 {
                                v___x_2240_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__28;
                                lean_inc(v___x_2237_);
                                v___x_2241_ = l_Lean_Syntax_isOfKind(v___x_2237_, v___x_2240_);
                                if v___x_2241_ == 0 {
                                    lean_dec(v___x_2237_);
                                    lean_dec(v_ty_2103_);
                                    lean_dec(v_id_2102_);
                                    lean_dec(v_tyName_2101_);
                                    v___x_2242_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                    v___x_2243_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2242_, v_a_2105_, v_a_2106_);
                                    lean_dec(v_config_2104_);
                                    return v___x_2243_;
                                } else {
                                    v___x_2244_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2230_);
                                    v___x_2245_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__30;
                                    lean_inc(v___x_2244_);
                                    v___x_2246_ = l_Lean_Syntax_isOfKind(v___x_2244_, v___x_2245_);
                                    if v___x_2246_ == 0 {
                                        lean_dec(v___x_2244_);
                                        lean_dec(v___x_2237_);
                                        lean_dec(v_ty_2103_);
                                        lean_dec(v_id_2102_);
                                        lean_dec(v_tyName_2101_);
                                        v___x_2247_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                        v___x_2248_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2247_, v_a_2105_, v_a_2106_);
                                        lean_dec(v_config_2104_);
                                        return v___x_2248_;
                                    } else {
                                        v___x_2249_ =
                                            l_Lean_Syntax_getArg(v___x_2244_, v___x_2233_);
                                        v___x_2250_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__32;
                                        lean_inc(v___x_2249_);
                                        v___x_2251_ =
                                            l_Lean_Syntax_isOfKind(v___x_2249_, v___x_2250_);
                                        if v___x_2251_ == 0 {
                                            lean_dec(v___x_2249_);
                                            lean_dec(v___x_2244_);
                                            lean_dec(v___x_2237_);
                                            lean_dec(v_ty_2103_);
                                            lean_dec(v_id_2102_);
                                            lean_dec(v_tyName_2101_);
                                            v___x_2252_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                            v___x_2253_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2252_, v_a_2105_, v_a_2106_);
                                            lean_dec(v_config_2104_);
                                            return v___x_2253_;
                                        } else {
                                            v_tk_2254_ =
                                                l_Lean_Syntax_getArg(v___x_2244_, v___x_2230_);
                                            lean_dec(v___x_2244_);
                                            v___x_2255_ =
                                                l_Lean_Syntax_getArg(v___x_2249_, v___x_2230_);
                                            lean_dec(v___x_2249_);
                                            v___x_2263_ =
                                                l_Lean_Syntax_getArg(v___x_2237_, v___x_2233_);
                                            lean_dec(v___x_2237_);
                                            v___x_2264_ = l_Lean_Syntax_isNone(v___x_2263_);
                                            if v___x_2264_ == 0 {
                                                lean_inc(v___x_2263_);
                                                v___x_2265_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2263_,
                                                    v___x_2233_,
                                                );
                                                if v___x_2265_ == 0 {
                                                    lean_dec(v___x_2263_);
                                                    lean_dec(v___x_2255_);
                                                    lean_dec(v_tk_2254_);
                                                    lean_dec(v_ty_2103_);
                                                    lean_dec(v_id_2102_);
                                                    lean_dec(v_tyName_2101_);
                                                    v___x_2266_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                                    v___x_2267_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2266_, v_a_2105_, v_a_2106_);
                                                    lean_dec(v_config_2104_);
                                                    return v___x_2267_;
                                                } else {
                                                    v_wds_x3f_2268_ = l_Lean_Syntax_getArg(
                                                        v___x_2263_,
                                                        v___x_2230_,
                                                    );
                                                    lean_dec(v___x_2263_);
                                                    v___x_2269_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                                    lean_inc(v_wds_x3f_2268_);
                                                    v___x_2270_ = l_Lean_Syntax_isOfKind(
                                                        v_wds_x3f_2268_,
                                                        v___x_2269_,
                                                    );
                                                    if v___x_2270_ == 0 {
                                                        lean_dec(v_wds_x3f_2268_);
                                                        lean_dec(v___x_2255_);
                                                        lean_dec(v_tk_2254_);
                                                        lean_dec(v_ty_2103_);
                                                        lean_dec(v_id_2102_);
                                                        lean_dec(v_tyName_2101_);
                                                        v___x_2271_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                                        v___x_2272_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2271_, v_a_2105_, v_a_2106_);
                                                        lean_dec(v_config_2104_);
                                                        return v___x_2272_;
                                                    } else {
                                                        v___x_2273_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(
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
                                                lean_dec(v___x_2263_);
                                                v___x_2274_ = lean_box(0);
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
                                lean_inc(v___x_2275_);
                                v___x_2277_ = l_Lean_Syntax_isOfKind(v___x_2275_, v___x_2276_);
                                if v___x_2277_ == 0 {
                                    lean_dec(v___x_2275_);
                                    lean_dec(v___x_2237_);
                                    lean_dec(v_ty_2103_);
                                    lean_dec(v_id_2102_);
                                    lean_dec(v_tyName_2101_);
                                    v___x_2278_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                    v___x_2279_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2278_, v_a_2105_, v_a_2106_);
                                    lean_dec(v_config_2104_);
                                    return v___x_2279_;
                                } else {
                                    v_tk_2280_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2230_);
                                    v___x_2281_ = l_Lean_Syntax_getArg(v___x_2275_, v___x_2230_);
                                    lean_dec(v___x_2275_);
                                    v___x_2289_ = lean_unsigned_to_nat(2);
                                    v___x_2290_ = l_Lean_Syntax_getArg(v___x_2237_, v___x_2289_);
                                    lean_dec(v___x_2237_);
                                    v___x_2291_ = l_Lean_Syntax_isNone(v___x_2290_);
                                    if v___x_2291_ == 0 {
                                        lean_inc(v___x_2290_);
                                        v___x_2292_ =
                                            l_Lean_Syntax_matchesNull(v___x_2290_, v___x_2233_);
                                        if v___x_2292_ == 0 {
                                            lean_dec(v___x_2290_);
                                            lean_dec(v___x_2281_);
                                            lean_dec(v_tk_2280_);
                                            lean_dec(v_ty_2103_);
                                            lean_dec(v_id_2102_);
                                            lean_dec(v_tyName_2101_);
                                            v___x_2293_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                            v___x_2294_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2293_, v_a_2105_, v_a_2106_);
                                            lean_dec(v_config_2104_);
                                            return v___x_2294_;
                                        } else {
                                            v_wds_x3f_2295_ =
                                                l_Lean_Syntax_getArg(v___x_2290_, v___x_2230_);
                                            lean_dec(v___x_2290_);
                                            v___x_2296_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                            lean_inc(v_wds_x3f_2295_);
                                            v___x_2297_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_2295_,
                                                v___x_2296_,
                                            );
                                            if v___x_2297_ == 0 {
                                                lean_dec(v_wds_x3f_2295_);
                                                lean_dec(v___x_2281_);
                                                lean_dec(v_tk_2280_);
                                                lean_dec(v_ty_2103_);
                                                lean_dec(v_id_2102_);
                                                lean_dec(v_tyName_2101_);
                                                v___x_2298_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__24);
                                                v___x_2299_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_config_2104_, v___x_2298_, v_a_2105_, v_a_2106_);
                                                lean_dec(v_config_2104_);
                                                return v___x_2299_;
                                            } else {
                                                v___x_2300_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_2300_, 0, v_wds_x3f_2295_);
                                                v_wds_x3f_2283_ = v___x_2300_;
                                                v___y_2284_ = v_a_2105_;
                                                v___y_2285_ = v_a_2106_;
                                                state = 13;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v___x_2290_);
                                        v___x_2301_ = lean_box(0);
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
                        lean_dec(v___x_2231_);
                        v___x_2302_ = lean_box(2);
                        v___x_2303_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8;
                        v___x_2304_ = lean_box(0);
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
                lean_inc_ref_n(v___y_2116_, 5);
                lean_inc_ref_n(v___y_2115_, 6);
                lean_inc_ref_n(v___y_2111_, 6);
                v___x_2118_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2117_);
                v___x_2119_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1;
                v___x_2120_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2119_);
                v___x_2121_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                v___x_2122_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                lean_inc_n(v___y_2109_, 8);
                v___x_2123_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2123_, 0, v___y_2109_);
                lean_ctor_set(v___x_2123_, 1, v___x_2121_);
                lean_ctor_set(v___x_2123_, 2, v___x_2122_);
                lean_inc_ref_n(v___x_2123_, 8);
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
                v___x_2128_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2128_, 0, v___y_2109_);
                lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                v___x_2129_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7;
                v___x_2130_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2129_);
                v___x_2131_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8;
                lean_inc_n(v___y_2114_, 2);
                v___x_2132_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2132_, 0, v___y_2114_);
                lean_ctor_set(v___x_2132_, 1, v___x_2121_);
                lean_ctor_set(v___x_2132_, 2, v___x_2131_);
                v___x_2133_ = lean_unsigned_to_nat(2);
                v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
                v___x_2135_ = lean_array_push(v___x_2134_, v_id_2102_);
                v___x_2136_ = lean_array_push(v___x_2135_, v___x_2132_);
                v___x_2137_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2137_, 0, v___y_2114_);
                lean_ctor_set(v___x_2137_, 1, v___x_2130_);
                lean_ctor_set(v___x_2137_, 2, v___x_2136_);
                v___x_2138_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9;
                v___x_2139_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___y_2116_, v___x_2138_);
                v___x_2140_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10;
                v___x_2141_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11;
                v___x_2142_ =
                    l_Lean_Name_mkStr4(v___y_2111_, v___y_2115_, v___x_2140_, v___x_2141_);
                v___x_2143_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12;
                v___x_2144_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2144_, 0, v___y_2109_);
                lean_ctor_set(v___x_2144_, 1, v___x_2143_);
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
                lean_inc(v___x_2149_);
                v___x_2150_ = lean_alloc_closure(
                    l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___x_2150_, 0, v___x_2149_);
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
                if lean_obj_tag(v___x_2162_) == 0 {
                    v_a_2163_ = lean_ctor_get(v___x_2162_, 0);
                    lean_inc(v_a_2163_);
                    lean_dec_ref_known(v___x_2162_, 1);
                    v___x_2164_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2157_);
                    if lean_obj_tag(v___x_2164_) == 0 {
                        lean_dec_ref_known(v___x_2164_, 1);
                        v_quotContext_x3f_2165_ = lean_ctor_get(v___y_2157_, 5);
                        v___x_2166_ = l_Lean_mkOptionalNode(v___y_2161_);
                        v___x_2167_ = lean_unsigned_to_nat(3);
                        v___x_2168_ = lean_mk_empty_array_with_capacity(v___x_2167_);
                        v___x_2169_ = lean_array_push(v___x_2168_, v___y_2160_);
                        v___x_2170_ = lean_array_push(v___x_2169_, v___y_2156_);
                        v___x_2171_ = lean_array_push(v___x_2170_, v___x_2166_);
                        v___x_2172_ = lean_box(2);
                        lean_inc(v___y_2153_);
                        v___x_2173_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v___x_2173_, 0, v___x_2172_);
                        lean_ctor_set(v___x_2173_, 1, v___y_2153_);
                        lean_ctor_set(v___x_2173_, 2, v___x_2171_);
                        v___x_2174_ = 0;
                        v___x_2175_ = l_Lean_SourceInfo_fromRef(v_a_2163_, v___x_2174_);
                        lean_dec(v_a_2163_);
                        if lean_obj_tag(v_quotContext_x3f_2165_) == 0 {
                            v___x_2176_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2155_);
                            lean_dec_ref(v___x_2176_);
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
                        lean_dec(v_a_2163_);
                        lean_dec(v___y_2161_);
                        lean_dec(v___y_2160_);
                        lean_dec(v___y_2156_);
                        lean_dec(v_config_2104_);
                        lean_dec(v_ty_2103_);
                        lean_dec(v_id_2102_);
                        v_a_2177_ = lean_ctor_get(v___x_2164_, 0);
                        v_isSharedCheck_2184_ = (!lean_is_exclusive(v___x_2164_)) as u8;
                        if v_isSharedCheck_2184_ == 0 {
                            v___x_2179_ = v___x_2164_;
                            v_isShared_2180_ = v_isSharedCheck_2184_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2177_);
                            lean_dec(v___x_2164_);
                            v___x_2179_ = lean_box(0);
                            v_isShared_2180_ = v_isSharedCheck_2184_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2161_);
                    lean_dec(v___y_2160_);
                    lean_dec(v___y_2156_);
                    lean_dec(v_config_2104_);
                    lean_dec(v_ty_2103_);
                    lean_dec(v_id_2102_);
                    v_a_2185_ = lean_ctor_get(v___x_2162_, 0);
                    v_isSharedCheck_2192_ = (!lean_is_exclusive(v___x_2162_)) as u8;
                    if v_isSharedCheck_2192_ == 0 {
                        v___x_2187_ = v___x_2162_;
                        v_isShared_2188_ = v_isSharedCheck_2192_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2185_);
                        lean_dec(v___x_2162_);
                        v___x_2187_ = lean_box(0);
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
                    v_reuseFailAlloc_2183_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_a_2177_);
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
                    v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
                    v___x_2190_ = v_reuseFailAlloc_2191_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2190_;
            }
            7 => {
                v_fieldMap_2200_ = lean_ctor_get(v___x_2193_, 1);
                v___x_2201_ = l___private_Lake_DSL_DeclUtil_0__Lake_DSL_mkConfigFields(
                    v_tyName_2101_,
                    v_fieldMap_2200_,
                    v_fs_2196_,
                    v___y_2198_,
                    v___y_2199_,
                );
                lean_dec_ref(v_fs_2196_);
                if lean_obj_tag(v___x_2201_) == 0 {
                    v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
                    lean_inc(v_a_2202_);
                    lean_dec_ref_known(v___x_2201_, 1);
                    v___x_2203_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__13;
                    v_whereTk_2204_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_whereTk_2204_, 0, v_whereInfo_2195_);
                    lean_ctor_set(v_whereTk_2204_, 1, v___x_2203_);
                    v___x_2205_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                    v___x_2206_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15;
                    v___x_2207_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                    v___x_2208_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__18;
                    if lean_obj_tag(v_wds_x3f_2197_) == 0 {
                        v___x_2209_ = lean_box(0);
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
                        v_val_2210_ = lean_ctor_get(v_wds_x3f_2197_, 0);
                        v_isSharedCheck_2217_ = (!lean_is_exclusive(v_wds_x3f_2197_)) as u8;
                        if v_isSharedCheck_2217_ == 0 {
                            v___x_2212_ = v_wds_x3f_2197_;
                            v_isShared_2213_ = v_isSharedCheck_2217_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_val_2210_);
                            lean_dec(v_wds_x3f_2197_);
                            v___x_2212_ = lean_box(0);
                            v_isShared_2213_ = v_isSharedCheck_2217_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_wds_x3f_2197_);
                    lean_dec(v_whereInfo_2195_);
                    lean_dec(v_config_2104_);
                    lean_dec(v_ty_2103_);
                    lean_dec(v_id_2102_);
                    v_a_2218_ = lean_ctor_get(v___x_2201_, 0);
                    v_isSharedCheck_2225_ = (!lean_is_exclusive(v___x_2201_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2220_ = v___x_2201_;
                        v_isShared_2221_ = v_isSharedCheck_2225_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2218_);
                        lean_dec(v___x_2201_);
                        v___x_2220_ = lean_box(0);
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
                    v_reuseFailAlloc_2216_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2216_, 0, v_val_2210_);
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
                    v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
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
                lean_dec(v___x_2255_);
                v___x_2261_ = l_Lean_Syntax_getHeadInfo(v_tk_2254_);
                lean_dec(v_tk_2254_);
                v___x_2262_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_2260_);
                lean_dec_ref(v_fs_2260_);
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
                lean_dec(v___x_2281_);
                v___x_2287_ = l_Lean_Syntax_getHeadInfo(v_tk_2280_);
                lean_dec(v_tk_2280_);
                v___x_2288_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_fs_2286_);
                lean_dec_ref(v_fs_2286_);
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
    mut v_tyName_2305_: *mut LeanObject,
    mut v_id_2306_: *mut LeanObject,
    mut v_ty_2307_: *mut LeanObject,
    mut v_config_2308_: *mut LeanObject,
    mut v_a_2309_: *mut LeanObject,
    mut v_a_2310_: *mut LeanObject,
    mut v_a_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2312_: *mut LeanObject = core::ptr::null_mut();
    v_res_2312_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v_tyName_2305_, v_id_2306_, v_ty_2307_, v_config_2308_, v_a_2309_, v_a_2310_);
    lean_dec(v_a_2310_);
    lean_dec_ref(v_a_2309_);
    return v_res_2312_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14()
-> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__13;
    v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20()
-> *mut LeanObject {
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    v___x_2341_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__19;
    v___x_2342_ = l_String_toRawSubstring_x27(v___x_2341_);
    return v___x_2342_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35()
-> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__34;
    v___x_2365_ = l_String_toRawSubstring_x27(v___x_2364_);
    return v___x_2365_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41()
-> *mut LeanObject {
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    v___x_2372_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__40;
    v___x_2373_ = l_String_toRawSubstring_x27(v___x_2372_);
    return v___x_2373_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44()
-> *mut LeanObject {
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    v___x_2377_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__43;
    v___x_2378_ = l_String_toRawSubstring_x27(v___x_2377_);
    return v___x_2378_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47()
-> *mut LeanObject {
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    v___x_2382_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__46;
    v___x_2383_ = l_String_toRawSubstring_x27(v___x_2382_);
    return v___x_2383_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54()
-> *mut LeanObject {
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    v___x_2391_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__53;
    v___x_2392_ = l_String_toRawSubstring_x27(v___x_2391_);
    return v___x_2392_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66()
-> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    v___x_2412_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__65;
    v___x_2413_ = l_String_toRawSubstring_x27(v___x_2412_);
    return v___x_2413_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(
    mut v_stx_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: u8 = 0;
    let mut v___y_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2593_: u8 = 0;
    let mut v_a_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2601_: u8 = 0;
    let mut v___y_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2607_: u8 = 0;
    let mut v___y_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: u8 = 0;
    let mut v___y_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2727_: u8 = 0;
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2731_: u8 = 0;
    let mut v_a_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2739_: u8 = 0;
    let mut v___y_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: u8 = 0;
    let mut v___y_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2797_: u8 = 0;
    let mut v_a_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2805_: u8 = 0;
    let mut v___y_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2808_: u8 = 0;
    let mut v___y_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v___y_2859_: u8 = 0;
    let mut v___y_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2892_: u8 = 0;
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2896_: u8 = 0;
    let mut v_kw_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2916_: u8 = 0;
    let mut v_ref_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2935_: u8 = 0;
    let mut v_a_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2939_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2943_: u8 = 0;
    let mut v_a_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2947_: u8 = 0;
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2951_: u8 = 0;
    let mut v___y_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_nameStx_x3f_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cfg_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: u8 = 0;
    let mut v___x_2987_: u8 = 0;
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nameStx_x3f_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2488_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12;
                lean_inc(v_stx_2416_);
                v___x_2489_ = l_Lean_Syntax_isOfKind(v_stx_2416_, v___x_2488_);
                if v___x_2489_ == 0 {
                    v___x_2490_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
                    v___x_2491_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_2416_, v___x_2490_, v_a_2417_, v_a_2418_);
                    lean_dec(v_stx_2416_);
                    return v___x_2491_;
                } else {
                    v___x_2492_ = lean_unsigned_to_nat(0);
                    v___x_2493_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2492_);
                    v___x_2494_ = lean_unsigned_to_nat(1);
                    v___x_2495_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2494_);
                    v___x_2496_ = lean_unsigned_to_nat(2);
                    v_kw_2897_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2496_);
                    v___x_2984_ = lean_unsigned_to_nat(3);
                    v___x_2985_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2984_);
                    v___x_2986_ = l_Lean_Syntax_isNone(v___x_2985_);
                    if v___x_2986_ == 0 {
                        lean_inc(v___x_2985_);
                        v___x_2987_ = l_Lean_Syntax_matchesNull(v___x_2985_, v___x_2494_);
                        if v___x_2987_ == 0 {
                            lean_dec(v___x_2985_);
                            lean_dec(v_kw_2897_);
                            lean_dec(v___x_2495_);
                            lean_dec(v___x_2493_);
                            v___x_2988_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__14);
                            v___x_2989_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_stx_2416_, v___x_2988_, v_a_2417_, v_a_2418_);
                            lean_dec(v_stx_2416_);
                            return v___x_2989_;
                        } else {
                            v_nameStx_x3f_2990_ = l_Lean_Syntax_getArg(v___x_2985_, v___x_2492_);
                            lean_dec(v___x_2985_);
                            v___x_2991_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2991_, 0, v_nameStx_x3f_2990_);
                            v_nameStx_x3f_2969_ = v___x_2991_;
                            v___y_2970_ = v_a_2417_;
                            v___y_2971_ = v_a_2418_;
                            state = 36;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2985_);
                        v___x_2992_ = lean_box(0);
                        v_nameStx_x3f_2969_ = v___x_2992_;
                        v___y_2970_ = v_a_2417_;
                        v___y_2971_ = v_a_2418_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_2432_);
                lean_inc_n(v___y_2421_, 5);
                lean_inc_n(v___y_2427_, 28);
                v___x_2445_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2445_, 0, v___y_2427_);
                lean_ctor_set(v___x_2445_, 1, v___y_2421_);
                lean_ctor_set(v___x_2445_, 2, v___y_2432_);
                lean_inc_ref(v___y_2444_);
                v___x_2446_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2446_, 0, v___y_2427_);
                lean_ctor_set(v___x_2446_, 1, v___y_2444_);
                lean_inc_ref_n(v___x_2445_, 12);
                v___x_2447_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2425_, v___x_2445_);
                v___x_2448_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__0;
                lean_inc_ref(v___y_2433_);
                v___x_2449_ = l_Lean_Name_mkStr2(v___y_2433_, v___x_2448_);
                v___x_2450_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2450_, 0, v___y_2427_);
                lean_ctor_set(v___x_2450_, 1, v___x_2448_);
                v___x_2451_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__2;
                v___x_2452_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__3;
                v___x_2453_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2453_, 0, v___y_2427_);
                lean_ctor_set(v___x_2453_, 1, v___x_2452_);
                v___x_2454_ = l_Lean_Syntax_node1(v___y_2427_, v___x_2451_, v___x_2453_);
                v___x_2455_ = l_Lean_Syntax_node1(v___y_2427_, v___y_2421_, v___x_2454_);
                v___x_2456_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__4;
                v___x_2457_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2457_, 0, v___y_2427_);
                lean_ctor_set(v___x_2457_, 1, v___x_2456_);
                v___x_2458_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__5;
                v___x_2459_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2459_, 0, v___y_2427_);
                lean_ctor_set(v___x_2459_, 1, v___x_2458_);
                lean_inc_ref(v___y_2435_);
                v___x_2460_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2460_, 0, v___y_2427_);
                lean_ctor_set(v___x_2460_, 1, v___y_2435_);
                v___x_2461_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__6;
                v___x_2462_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2462_, 0, v___y_2427_);
                lean_ctor_set(v___x_2462_, 1, v___x_2461_);
                v___x_2463_ = l_Lean_Syntax_node1(v___y_2427_, v___x_2451_, v___x_2462_);
                v___x_2464_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__7;
                v___x_2465_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2465_, 0, v___y_2427_);
                lean_ctor_set(v___x_2465_, 1, v___x_2464_);
                lean_inc_ref(v___x_2460_);
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
                lean_inc_ref(v___y_2424_);
                v___x_2470_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2470_, 0, v___y_2427_);
                lean_ctor_set(v___x_2470_, 1, v___y_2424_);
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
                v___x_2474_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2474_, 0, v___y_2427_);
                lean_ctor_set(v___x_2474_, 1, v___y_2438_);
                v___x_2475_ = lean_array_push(v___y_2422_, v___y_2430_);
                v___x_2476_ = lean_array_push(v___x_2475_, v___y_2431_);
                v___x_2477_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2477_, 0, v___y_2423_);
                lean_ctor_set(v___x_2477_, 1, v___y_2443_);
                lean_ctor_set(v___x_2477_, 2, v___x_2476_);
                v___x_2478_ =
                    l_Lean_Syntax_node2(v___y_2427_, v___y_2442_, v___x_2445_, v___x_2445_);
                v___x_2479_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__9;
                v___x_2480_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__10;
                v___x_2481_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2481_, 0, v___y_2427_);
                lean_ctor_set(v___x_2481_, 1, v___x_2480_);
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
                lean_dec_ref(v___y_2436_);
                return v___x_2487_;
            }
            2 => {
                lean_inc_ref_n(v___y_2517_, 3);
                v___x_2524_ = l_Array_append___redArg(v___y_2517_, v___y_2523_);
                lean_dec_ref(v___y_2523_);
                lean_inc_n(v___y_2499_, 6);
                lean_inc_n(v___y_2515_, 18);
                v___x_2525_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2525_, 0, v___y_2515_);
                lean_ctor_set(v___x_2525_, 1, v___y_2499_);
                lean_ctor_set(v___x_2525_, 2, v___x_2524_);
                v___x_2526_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15;
                lean_inc_ref(v___y_2510_);
                lean_inc_ref_n(v___y_2518_, 6);
                lean_inc_ref_n(v___y_2506_, 7);
                v___x_2527_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2510_, v___x_2526_);
                v___x_2528_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16;
                v___x_2529_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2529_, 0, v___y_2515_);
                lean_ctor_set(v___x_2529_, 1, v___x_2528_);
                lean_inc_ref(v___y_2519_);
                v___x_2530_ = l_Lean_Syntax_SepArray_ofElems(v___y_2519_, v___y_2513_);
                lean_dec_ref(v___y_2513_);
                v___x_2531_ = l_Array_append___redArg(v___y_2517_, v___x_2530_);
                lean_dec_ref(v___x_2530_);
                v___x_2532_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2532_, 0, v___y_2515_);
                lean_ctor_set(v___x_2532_, 1, v___y_2499_);
                lean_ctor_set(v___x_2532_, 2, v___x_2531_);
                v___x_2533_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17;
                v___x_2534_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2534_, 0, v___y_2515_);
                lean_ctor_set(v___x_2534_, 1, v___x_2533_);
                lean_inc(v___x_2527_);
                v___x_2535_ = l_Lean_Syntax_node3(
                    v___y_2515_,
                    v___x_2527_,
                    v___x_2529_,
                    v___x_2532_,
                    v___x_2534_,
                );
                v___x_2536_ = l_Lean_Syntax_node1(v___y_2515_, v___y_2499_, v___x_2535_);
                v___x_2537_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2537_, 0, v___y_2515_);
                lean_ctor_set(v___x_2537_, 1, v___y_2499_);
                lean_ctor_set(v___x_2537_, 2, v___y_2517_);
                lean_inc_ref_n(v___x_2537_, 8);
                lean_inc(v___y_2516_);
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
                lean_inc_ref_n(v___y_2501_, 3);
                v___x_2540_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2539_);
                v___x_2541_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2541_, 0, v___y_2515_);
                lean_ctor_set(v___x_2541_, 1, v___x_2539_);
                v___x_2542_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7;
                v___x_2543_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2542_);
                v___x_2544_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__8;
                lean_inc_n(v___y_2511_, 2);
                v___x_2545_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2545_, 0, v___y_2511_);
                lean_ctor_set(v___x_2545_, 1, v___y_2499_);
                lean_ctor_set(v___x_2545_, 2, v___x_2544_);
                v___x_2546_ = lean_mk_empty_array_with_capacity(v___x_2496_);
                lean_inc(v___y_2505_);
                lean_inc_ref(v___x_2546_);
                v___x_2547_ = lean_array_push(v___x_2546_, v___y_2505_);
                lean_inc_ref(v___x_2545_);
                v___x_2548_ = lean_array_push(v___x_2547_, v___x_2545_);
                lean_inc(v___x_2543_);
                v___x_2549_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2549_, 0, v___y_2511_);
                lean_ctor_set(v___x_2549_, 1, v___x_2543_);
                lean_ctor_set(v___x_2549_, 2, v___x_2548_);
                v___x_2550_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9;
                v___x_2551_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2550_);
                v___x_2552_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11;
                v___x_2553_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2510_, v___x_2552_);
                v___x_2554_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12;
                v___x_2555_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2555_, 0, v___y_2515_);
                lean_ctor_set(v___x_2555_, 1, v___x_2554_);
                v___x_2556_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__20);
                v___x_2557_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__21;
                v___x_2558_ = l_Lean_addMacroScope(v___y_2504_, v___x_2557_, v___y_2498_);
                v___x_2559_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__23;
                v___x_2560_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__24;
                lean_inc(v___y_2502_);
                v___x_2561_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2561_, 0, v___x_2560_);
                lean_ctor_set(v___x_2561_, 1, v___y_2502_);
                v___x_2562_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2562_, 0, v___x_2559_);
                lean_ctor_set(v___x_2562_, 1, v___x_2561_);
                v___x_2563_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2563_, 0, v___y_2515_);
                lean_ctor_set(v___x_2563_, 1, v___x_2556_);
                lean_ctor_set(v___x_2563_, 2, v___x_2558_);
                lean_ctor_set(v___x_2563_, 3, v___x_2562_);
                v___x_2564_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___x_2553_, v___x_2555_, v___x_2563_);
                v___x_2565_ = l_Lean_Syntax_node1(v___y_2515_, v___y_2499_, v___x_2564_);
                lean_inc(v___x_2551_);
                v___x_2566_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___x_2551_, v___x_2537_, v___x_2565_);
                v___x_2567_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25;
                v___x_2568_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___y_2501_, v___x_2567_);
                lean_inc_ref(v___y_2507_);
                v___x_2569_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2569_, 0, v___y_2515_);
                lean_ctor_set(v___x_2569_, 1, v___y_2507_);
                v___x_2570_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26;
                v___x_2571_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27;
                v___x_2572_ =
                    l_Lean_Name_mkStr4(v___y_2506_, v___y_2518_, v___x_2570_, v___x_2571_);
                lean_inc(v___x_2572_);
                v___x_2573_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___x_2572_, v___x_2537_, v___x_2537_);
                lean_inc(v___x_2568_);
                v___x_2574_ = l_Lean_Syntax_node4(
                    v___y_2515_,
                    v___x_2568_,
                    v___x_2569_,
                    v___y_2509_,
                    v___x_2573_,
                    v___x_2537_,
                );
                lean_inc(v___x_2540_);
                v___x_2575_ = l_Lean_Syntax_node4(
                    v___y_2515_,
                    v___x_2540_,
                    v___x_2541_,
                    v___x_2549_,
                    v___x_2566_,
                    v___x_2574_,
                );
                lean_inc(v___y_2508_);
                v___x_2576_ =
                    l_Lean_Syntax_node2(v___y_2515_, v___y_2508_, v___x_2538_, v___x_2575_);
                lean_inc(v___x_2576_);
                v___x_2577_ = lean_alloc_closure(
                    l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___x_2577_, 0, v___x_2576_);
                v___x_2578_ = l_Lean_Elab_Command_withMacroExpansion___redArg(
                    v_stx_2416_,
                    v___x_2576_,
                    v___x_2577_,
                    v___y_2520_,
                    v___y_2521_,
                );
                if lean_obj_tag(v___x_2578_) == 0 {
                    lean_dec_ref_known(v___x_2578_, 1);
                    v___x_2579_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                            v___y_2520_,
                            v___y_2521_,
                        );
                    if lean_obj_tag(v___x_2579_) == 0 {
                        v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
                        lean_inc(v_a_2580_);
                        lean_dec_ref_known(v___x_2579_, 1);
                        v___x_2581_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2520_);
                        if lean_obj_tag(v___x_2581_) == 0 {
                            lean_dec_ref_known(v___x_2581_, 1);
                            v___x_2582_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__28;
                            v___x_2583_ = l_Lean_Name_str___override(v___y_2503_, v___x_2582_);
                            v___x_2584_ = l_Lean_mkIdentFrom(v___y_2505_, v___x_2583_, v___y_2500_);
                            lean_dec(v___y_2505_);
                            if lean_obj_tag(v___y_2512_) == 0 {
                                v___x_2585_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2521_);
                                lean_dec_ref(v___x_2585_);
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
                                lean_dec_ref_known(v___y_2512_, 1);
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
                            lean_dec(v_a_2580_);
                            lean_dec(v___x_2572_);
                            lean_dec(v___x_2568_);
                            lean_dec(v___x_2551_);
                            lean_dec_ref(v___x_2546_);
                            lean_dec_ref_known(v___x_2545_, 3);
                            lean_dec(v___x_2543_);
                            lean_dec(v___x_2540_);
                            lean_dec(v___x_2527_);
                            lean_dec(v___y_2522_);
                            lean_dec_ref(v___y_2520_);
                            lean_dec(v___y_2516_);
                            lean_dec(v___y_2514_);
                            lean_dec(v___y_2512_);
                            lean_dec(v___y_2511_);
                            lean_dec(v___y_2508_);
                            lean_dec(v___y_2505_);
                            lean_dec(v___y_2503_);
                            v_a_2586_ = lean_ctor_get(v___x_2581_, 0);
                            v_isSharedCheck_2593_ = (!lean_is_exclusive(v___x_2581_)) as u8;
                            if v_isSharedCheck_2593_ == 0 {
                                v___x_2588_ = v___x_2581_;
                                v_isShared_2589_ = v_isSharedCheck_2593_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2586_);
                                lean_dec(v___x_2581_);
                                v___x_2588_ = lean_box(0);
                                v_isShared_2589_ = v_isSharedCheck_2593_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2572_);
                        lean_dec(v___x_2568_);
                        lean_dec(v___x_2551_);
                        lean_dec_ref(v___x_2546_);
                        lean_dec_ref_known(v___x_2545_, 3);
                        lean_dec(v___x_2543_);
                        lean_dec(v___x_2540_);
                        lean_dec(v___x_2527_);
                        lean_dec(v___y_2522_);
                        lean_dec_ref(v___y_2520_);
                        lean_dec(v___y_2516_);
                        lean_dec(v___y_2514_);
                        lean_dec(v___y_2512_);
                        lean_dec(v___y_2511_);
                        lean_dec(v___y_2508_);
                        lean_dec(v___y_2505_);
                        lean_dec(v___y_2503_);
                        v_a_2594_ = lean_ctor_get(v___x_2579_, 0);
                        v_isSharedCheck_2601_ = (!lean_is_exclusive(v___x_2579_)) as u8;
                        if v_isSharedCheck_2601_ == 0 {
                            v___x_2596_ = v___x_2579_;
                            v_isShared_2597_ = v_isSharedCheck_2601_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2594_);
                            lean_dec(v___x_2579_);
                            v___x_2596_ = lean_box(0);
                            v_isShared_2597_ = v_isSharedCheck_2601_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2572_);
                    lean_dec(v___x_2568_);
                    lean_dec(v___x_2551_);
                    lean_dec_ref(v___x_2546_);
                    lean_dec_ref_known(v___x_2545_, 3);
                    lean_dec(v___x_2543_);
                    lean_dec(v___x_2540_);
                    lean_dec(v___x_2527_);
                    lean_dec(v___y_2522_);
                    lean_dec_ref(v___y_2520_);
                    lean_dec(v___y_2516_);
                    lean_dec(v___y_2514_);
                    lean_dec(v___y_2512_);
                    lean_dec(v___y_2511_);
                    lean_dec(v___y_2508_);
                    lean_dec(v___y_2505_);
                    lean_dec(v___y_2503_);
                    return v___x_2578_;
                }
            }
            3 => {
                if v_isShared_2589_ == 0 {
                    v___x_2591_ = v___x_2588_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_a_2586_);
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
                    v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
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
                lean_inc_ref_n(v___y_2618_, 2);
                lean_inc_ref_n(v___y_2617_, 2);
                v___x_2628_ =
                    l_Lean_Name_mkStr4(v___y_2617_, v___y_2618_, v___x_2626_, v___x_2627_);
                v___x_2629_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1;
                v___x_2630_ =
                    l_Lean_Name_mkStr4(v___y_2617_, v___y_2618_, v___x_2626_, v___x_2629_);
                if lean_obj_tag(v___y_2622_) == 1 {
                    v_val_2631_ = lean_ctor_get(v___y_2622_, 0);
                    lean_inc(v_val_2631_);
                    lean_dec_ref_known(v___y_2622_, 1);
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
                    lean_dec(v___y_2622_);
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
                lean_inc_ref_n(v___y_2636_, 6);
                lean_inc_ref_n(v___y_2651_, 6);
                lean_inc_ref_n(v___y_2650_, 6);
                v___x_2660_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2659_);
                v___x_2661_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31;
                lean_inc_n(v___y_2640_, 28);
                v___x_2662_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2662_, 0, v___y_2640_);
                lean_ctor_set(v___x_2662_, 1, v___x_2661_);
                lean_inc_ref(v___y_2648_);
                lean_inc_n(v___y_2635_, 6);
                v___x_2663_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2663_, 0, v___y_2640_);
                lean_ctor_set(v___x_2663_, 1, v___y_2635_);
                lean_ctor_set(v___x_2663_, 2, v___y_2648_);
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
                v___x_2670_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__35);
                v___x_2671_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__36;
                lean_inc_n(v___y_2652_, 3);
                lean_inc_n(v_a_2658_, 3);
                v___x_2672_ = l_Lean_addMacroScope(v_a_2658_, v___x_2671_, v___y_2652_);
                lean_inc_n(v___y_2646_, 4);
                v___x_2673_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2673_, 0, v___y_2640_);
                lean_ctor_set(v___x_2673_, 1, v___x_2670_);
                lean_ctor_set(v___x_2673_, 2, v___x_2672_);
                lean_ctor_set(v___x_2673_, 3, v___y_2646_);
                lean_inc_ref_n(v___x_2663_, 18);
                lean_inc_n(v___x_2669_, 3);
                v___x_2674_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2669_, v___x_2673_, v___x_2663_);
                v___x_2675_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__37;
                v___x_2676_ =
                    l_Lean_Name_mkStr4(v___y_2650_, v___y_2651_, v___y_2636_, v___x_2675_);
                v___x_2677_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38;
                v___x_2678_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2678_, 0, v___y_2640_);
                lean_ctor_set(v___x_2678_, 1, v___x_2677_);
                lean_inc_ref_n(v___x_2678_, 3);
                lean_inc_n(v___x_2676_, 3);
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
                lean_inc_n(v___x_2667_, 3);
                v___x_2681_ =
                    l_Lean_Syntax_node2(v___y_2640_, v___x_2667_, v___x_2674_, v___x_2680_);
                v___x_2682_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39;
                v___x_2683_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2683_, 0, v___y_2640_);
                lean_ctor_set(v___x_2683_, 1, v___x_2682_);
                v___x_2684_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__41);
                v___x_2685_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__42;
                v___x_2686_ = l_Lean_addMacroScope(v_a_2658_, v___x_2685_, v___y_2652_);
                v___x_2687_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2687_, 0, v___y_2640_);
                lean_ctor_set(v___x_2687_, 1, v___x_2684_);
                lean_ctor_set(v___x_2687_, 2, v___x_2686_);
                lean_ctor_set(v___x_2687_, 3, v___y_2646_);
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
                v___x_2692_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__44);
                v___x_2693_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__45;
                v___x_2694_ = l_Lean_addMacroScope(v_a_2658_, v___x_2693_, v___y_2652_);
                v___x_2695_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2695_, 0, v___y_2640_);
                lean_ctor_set(v___x_2695_, 1, v___x_2692_);
                lean_ctor_set(v___x_2695_, 2, v___x_2694_);
                lean_ctor_set(v___x_2695_, 3, v___y_2646_);
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
                v___x_2700_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__47);
                v___x_2701_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__48;
                v___x_2702_ = l_Lean_addMacroScope(v_a_2658_, v___x_2701_, v___y_2652_);
                v___x_2703_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2703_, 0, v___y_2640_);
                lean_ctor_set(v___x_2703_, 1, v___x_2700_);
                lean_ctor_set(v___x_2703_, 2, v___x_2702_);
                lean_ctor_set(v___x_2703_, 3, v___y_2646_);
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
                lean_inc_ref_n(v___x_2683_, 2);
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
                v___x_2714_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2714_, 0, v___y_2640_);
                lean_ctor_set(v___x_2714_, 1, v___x_2713_);
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
                if lean_obj_tag(v___x_2716_) == 0 {
                    v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
                    lean_inc(v_a_2717_);
                    lean_dec_ref_known(v___x_2716_, 1);
                    v___x_2718_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2653_);
                    if lean_obj_tag(v___x_2718_) == 0 {
                        if lean_obj_tag(v___y_2642_) == 0 {
                            v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
                            lean_inc(v_a_2719_);
                            lean_dec_ref_known(v___x_2718_, 1);
                            v___x_2720_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2656_);
                            v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
                            lean_inc(v_a_2721_);
                            lean_dec_ref(v___x_2720_);
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
                            v_a_2722_ = lean_ctor_get(v___x_2718_, 0);
                            lean_inc(v_a_2722_);
                            lean_dec_ref_known(v___x_2718_, 1);
                            v_val_2723_ = lean_ctor_get(v___y_2642_, 0);
                            lean_inc(v_val_2723_);
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
                        lean_dec(v_a_2717_);
                        lean_dec(v___x_2715_);
                        lean_dec(v___y_2657_);
                        lean_dec(v___y_2654_);
                        lean_dec_ref(v___y_2653_);
                        lean_dec_ref(v___y_2651_);
                        lean_dec(v___y_2647_);
                        lean_dec(v___y_2645_);
                        lean_dec(v___y_2644_);
                        lean_dec_ref(v___y_2643_);
                        lean_dec(v___y_2642_);
                        lean_dec(v___y_2641_);
                        lean_dec_ref(v___y_2636_);
                        lean_dec(v_stx_2416_);
                        v_a_2724_ = lean_ctor_get(v___x_2718_, 0);
                        v_isSharedCheck_2731_ = (!lean_is_exclusive(v___x_2718_)) as u8;
                        if v_isSharedCheck_2731_ == 0 {
                            v___x_2726_ = v___x_2718_;
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2724_);
                            lean_dec(v___x_2718_);
                            v___x_2726_ = lean_box(0);
                            v_isShared_2727_ = v_isSharedCheck_2731_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2715_);
                    lean_dec(v___y_2657_);
                    lean_dec(v___y_2654_);
                    lean_dec_ref(v___y_2653_);
                    lean_dec_ref(v___y_2651_);
                    lean_dec(v___y_2647_);
                    lean_dec(v___y_2645_);
                    lean_dec(v___y_2644_);
                    lean_dec_ref(v___y_2643_);
                    lean_dec(v___y_2642_);
                    lean_dec(v___y_2641_);
                    lean_dec_ref(v___y_2636_);
                    lean_dec(v_stx_2416_);
                    v_a_2732_ = lean_ctor_get(v___x_2716_, 0);
                    v_isSharedCheck_2739_ = (!lean_is_exclusive(v___x_2716_)) as u8;
                    if v_isSharedCheck_2739_ == 0 {
                        v___x_2734_ = v___x_2716_;
                        v_isShared_2735_ = v_isSharedCheck_2739_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2732_);
                        lean_dec(v___x_2716_);
                        v___x_2734_ = lean_box(0);
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
                    v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
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
                    v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
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
                lean_inc_ref_n(v___y_2750_, 2);
                v___x_2761_ =
                    l_Lean_Name_mkStr4(v___y_2750_, v___x_2758_, v___x_2759_, v___x_2760_);
                v___x_2762_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52;
                v___x_2763_ =
                    l_Lean_Name_mkStr4(v___y_2750_, v___x_2758_, v___x_2759_, v___x_2762_);
                v___x_2764_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                v___x_2765_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                lean_inc_n(v___y_2756_, 2);
                v___x_2766_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2766_, 0, v___y_2756_);
                lean_ctor_set(v___x_2766_, 1, v___x_2764_);
                lean_ctor_set(v___x_2766_, 2, v___x_2765_);
                lean_inc_ref(v___x_2766_);
                lean_inc(v___x_2763_);
                v___x_2767_ = l_Lean_Syntax_node1(v___y_2756_, v___x_2763_, v___x_2766_);
                v___x_2768_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                    v___y_2751_,
                    v___y_2755_,
                );
                if lean_obj_tag(v___x_2768_) == 0 {
                    v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
                    lean_inc(v_a_2769_);
                    lean_dec_ref_known(v___x_2768_, 1);
                    v___x_2770_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2751_);
                    if lean_obj_tag(v___x_2770_) == 0 {
                        v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
                        lean_inc(v_a_2771_);
                        lean_dec_ref_known(v___x_2770_, 1);
                        v___x_2772_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__54);
                        v___x_2773_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__56;
                        v___x_2774_ = l_Lean_addMacroScope(v_a_2757_, v___x_2773_, v___y_2747_);
                        lean_inc(v___y_2748_);
                        lean_inc_n(v___y_2756_, 2);
                        v___x_2775_ = lean_alloc_ctor(3, 4, (0) as u32);
                        lean_ctor_set(v___x_2775_, 0, v___y_2756_);
                        lean_ctor_set(v___x_2775_, 1, v___x_2772_);
                        lean_ctor_set(v___x_2775_, 2, v___x_2774_);
                        lean_ctor_set(v___x_2775_, 3, v___y_2748_);
                        v___x_2776_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57;
                        v___x_2777_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58;
                        lean_inc_ref(v___y_2750_);
                        v___x_2778_ =
                            l_Lean_Name_mkStr4(v___y_2750_, v___x_2758_, v___x_2776_, v___x_2777_);
                        v___x_2779_ =
                            l_Lean_Syntax_node2(v___y_2756_, v___x_2778_, v___x_2775_, v___x_2766_);
                        lean_inc(v___x_2761_);
                        v___x_2780_ =
                            l_Lean_Syntax_node2(v___y_2756_, v___x_2761_, v___x_2767_, v___x_2779_);
                        v___x_2781_ = lean_mk_empty_array_with_capacity(v___x_2494_);
                        v___x_2782_ = lean_array_push(v___x_2781_, v___x_2780_);
                        v___x_2783_ = l_Lake_DSL_expandAttrs(v___y_2754_);
                        v___x_2784_ = l_Array_append___redArg(v___x_2782_, v___x_2783_);
                        lean_dec_ref(v___x_2783_);
                        v___x_2785_ = l_Lake_DSL_packageDeclName;
                        v___x_2786_ = l_Lean_mkIdentFrom(v___y_2745_, v___x_2785_, v___y_2742_);
                        lean_dec(v___y_2745_);
                        if lean_obj_tag(v___y_2746_) == 0 {
                            v___x_2787_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2755_);
                            v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
                            lean_inc(v_a_2788_);
                            lean_dec_ref(v___x_2787_);
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
                            v_val_2789_ = lean_ctor_get(v___y_2746_, 0);
                            lean_inc(v_val_2789_);
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
                        lean_dec(v_a_2769_);
                        lean_dec(v___x_2767_);
                        lean_dec_ref_known(v___x_2766_, 3);
                        lean_dec(v___x_2763_);
                        lean_dec(v___x_2761_);
                        lean_dec(v_a_2757_);
                        lean_dec(v___y_2756_);
                        lean_dec(v___y_2754_);
                        lean_dec(v___y_2753_);
                        lean_dec(v___y_2752_);
                        lean_dec_ref(v___y_2751_);
                        lean_dec(v___y_2749_);
                        lean_dec(v___y_2747_);
                        lean_dec(v___y_2746_);
                        lean_dec(v___y_2745_);
                        lean_dec(v___y_2744_);
                        lean_dec(v___y_2743_);
                        lean_dec(v___y_2741_);
                        lean_dec(v_stx_2416_);
                        v_a_2790_ = lean_ctor_get(v___x_2770_, 0);
                        v_isSharedCheck_2797_ = (!lean_is_exclusive(v___x_2770_)) as u8;
                        if v_isSharedCheck_2797_ == 0 {
                            v___x_2792_ = v___x_2770_;
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2790_);
                            lean_dec(v___x_2770_);
                            v___x_2792_ = lean_box(0);
                            v_isShared_2793_ = v_isSharedCheck_2797_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2767_);
                    lean_dec_ref_known(v___x_2766_, 3);
                    lean_dec(v___x_2763_);
                    lean_dec(v___x_2761_);
                    lean_dec(v_a_2757_);
                    lean_dec(v___y_2756_);
                    lean_dec(v___y_2754_);
                    lean_dec(v___y_2753_);
                    lean_dec(v___y_2752_);
                    lean_dec_ref(v___y_2751_);
                    lean_dec(v___y_2749_);
                    lean_dec(v___y_2747_);
                    lean_dec(v___y_2746_);
                    lean_dec(v___y_2745_);
                    lean_dec(v___y_2744_);
                    lean_dec(v___y_2743_);
                    lean_dec(v___y_2741_);
                    lean_dec(v_stx_2416_);
                    v_a_2798_ = lean_ctor_get(v___x_2768_, 0);
                    v_isSharedCheck_2805_ = (!lean_is_exclusive(v___x_2768_)) as u8;
                    if v_isSharedCheck_2805_ == 0 {
                        v___x_2800_ = v___x_2768_;
                        v_isShared_2801_ = v_isSharedCheck_2805_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_2798_);
                        lean_dec(v___x_2768_);
                        v___x_2800_ = lean_box(0);
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
                    v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
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
                    v_reuseFailAlloc_2804_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_a_2798_);
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
                v___x_2821_ = lean_box(2);
                v___x_2822_ = l_Lean_Syntax_mkNumLit(v___x_2820_, v___x_2821_);
                v___x_2823_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                v___x_2824_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__61;
                v___x_2825_ = lean_mk_empty_array_with_capacity(v___x_2496_);
                lean_inc(v___y_2819_);
                lean_inc_ref(v___x_2825_);
                v___x_2826_ = lean_array_push(v___x_2825_, v___y_2819_);
                v___x_2827_ = lean_array_push(v___x_2826_, v___x_2822_);
                v___x_2828_ = l_Lean_Syntax_mkCApp(v___x_2824_, v___x_2827_);
                v___x_2829_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__63;
                lean_inc(v___x_2828_);
                v___x_2830_ = lean_array_push(v___x_2825_, v___x_2828_);
                lean_inc(v___y_2807_);
                v___x_2831_ = lean_array_push(v___x_2830_, v___y_2807_);
                v___x_2832_ = l_Lean_Syntax_mkCApp(v___x_2829_, v___x_2831_);
                lean_inc(v___y_2812_);
                v___x_2833_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1(v___x_2829_, v___y_2812_, v___x_2832_, v___y_2814_, v___y_2815_, v___y_2818_);
                if lean_obj_tag(v___x_2833_) == 0 {
                    lean_dec_ref_known(v___x_2833_, 1);
                    v___x_2834_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___lam__0(
                            v___y_2815_,
                            v___y_2818_,
                        );
                    if lean_obj_tag(v___x_2834_) == 0 {
                        v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
                        lean_inc(v_a_2835_);
                        lean_dec_ref_known(v___x_2834_, 1);
                        v___x_2836_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2815_);
                        if lean_obj_tag(v___x_2836_) == 0 {
                            if lean_obj_tag(v___y_2810_) == 0 {
                                v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
                                lean_inc(v_a_2837_);
                                lean_dec_ref_known(v___x_2836_, 1);
                                v___x_2838_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2818_);
                                v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
                                lean_inc(v_a_2839_);
                                lean_dec_ref(v___x_2838_);
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
                                v_a_2840_ = lean_ctor_get(v___x_2836_, 0);
                                lean_inc(v_a_2840_);
                                lean_dec_ref_known(v___x_2836_, 1);
                                v_val_2841_ = lean_ctor_get(v___y_2810_, 0);
                                lean_inc(v_val_2841_);
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
                            lean_dec(v_a_2835_);
                            lean_dec(v___x_2828_);
                            lean_dec(v___y_2819_);
                            lean_dec(v___y_2817_);
                            lean_dec(v___y_2816_);
                            lean_dec_ref(v___y_2815_);
                            lean_dec(v___y_2812_);
                            lean_dec(v___y_2810_);
                            lean_dec(v___y_2809_);
                            lean_dec(v___y_2807_);
                            lean_dec(v_stx_2416_);
                            v_a_2842_ = lean_ctor_get(v___x_2836_, 0);
                            v_isSharedCheck_2849_ = (!lean_is_exclusive(v___x_2836_)) as u8;
                            if v_isSharedCheck_2849_ == 0 {
                                v___x_2844_ = v___x_2836_;
                                v_isShared_2845_ = v_isSharedCheck_2849_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_2842_);
                                lean_dec(v___x_2836_);
                                v___x_2844_ = lean_box(0);
                                v_isShared_2845_ = v_isSharedCheck_2849_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_2828_);
                        lean_dec(v___y_2819_);
                        lean_dec(v___y_2817_);
                        lean_dec(v___y_2816_);
                        lean_dec_ref(v___y_2815_);
                        lean_dec(v___y_2812_);
                        lean_dec(v___y_2810_);
                        lean_dec(v___y_2809_);
                        lean_dec(v___y_2807_);
                        lean_dec(v_stx_2416_);
                        v_a_2850_ = lean_ctor_get(v___x_2834_, 0);
                        v_isSharedCheck_2857_ = (!lean_is_exclusive(v___x_2834_)) as u8;
                        if v_isSharedCheck_2857_ == 0 {
                            v___x_2852_ = v___x_2834_;
                            v_isShared_2853_ = v_isSharedCheck_2857_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_2850_);
                            lean_dec(v___x_2834_);
                            v___x_2852_ = lean_box(0);
                            v_isShared_2853_ = v_isSharedCheck_2857_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2828_);
                    lean_dec(v___y_2819_);
                    lean_dec(v___y_2817_);
                    lean_dec(v___y_2816_);
                    lean_dec_ref(v___y_2815_);
                    lean_dec(v___y_2812_);
                    lean_dec(v___y_2810_);
                    lean_dec(v___y_2809_);
                    lean_dec(v___y_2807_);
                    lean_dec(v_stx_2416_);
                    return v___x_2833_;
                }
            }
            19 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
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
                    v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
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
                if lean_obj_tag(v___x_2870_) == 0 {
                    v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
                    lean_inc_n(v_a_2871_, 2);
                    lean_dec_ref_known(v___x_2870_, 1);
                    v___x_2872_ = lean_st_ref_get(v___y_2866_);
                    v_env_2873_ = lean_ctor_get(v___x_2872_, 0);
                    lean_inc_ref(v_env_2873_);
                    lean_dec(v___x_2872_);
                    v___x_2874_ = l_Lake_nameExt;
                    v_asyncMode_2875_ = lean_ctor_get(v___x_2874_, 2);
                    v___x_2876_ = lean_box(0);
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
                    v_fst_2879_ = lean_ctor_get(v___x_2878_, 0);
                    lean_inc(v_fst_2879_);
                    v_snd_2880_ = lean_ctor_get(v___x_2878_, 1);
                    lean_inc(v_snd_2880_);
                    lean_dec(v___x_2878_);
                    v___x_2881_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__66);
                    v___x_2882_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__67;
                    v___x_2883_ = l_Lean_addMacroScope(v_a_2869_, v___x_2882_, v___y_2867_);
                    v___x_2884_ = lean_box(0);
                    v___x_2885_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_2885_, 0, v___y_2868_);
                    lean_ctor_set(v___x_2885_, 1, v___x_2881_);
                    lean_ctor_set(v___x_2885_, 2, v___x_2883_);
                    lean_ctor_set(v___x_2885_, 3, v___x_2884_);
                    v___x_2886_ = l_Lean_TSyntax_getId(v_a_2871_);
                    v___x_2887_ = l_Lake_Name_quoteFrom(v_a_2871_, v___x_2886_, v___y_2859_);
                    if lean_obj_tag(v_snd_2880_) == 0 {
                        lean_inc(v___x_2887_);
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
                        lean_inc(v_a_2871_);
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
                    lean_dec(v_a_2869_);
                    lean_dec(v___y_2868_);
                    lean_dec(v___y_2867_);
                    lean_dec(v___y_2865_);
                    lean_dec(v___y_2864_);
                    lean_dec(v___y_2863_);
                    lean_dec_ref(v___y_2862_);
                    lean_dec(v___y_2861_);
                    lean_dec(v_stx_2416_);
                    v_a_2889_ = lean_ctor_get(v___x_2870_, 0);
                    v_isSharedCheck_2896_ = (!lean_is_exclusive(v___x_2870_)) as u8;
                    if v_isSharedCheck_2896_ == 0 {
                        v___x_2891_ = v___x_2870_;
                        v_isShared_2892_ = v_isSharedCheck_2896_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_2889_);
                        lean_dec(v___x_2870_);
                        v___x_2891_ = lean_box(0);
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
                    v_reuseFailAlloc_2895_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
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
                if lean_obj_tag(v___x_2905_) == 0 {
                    v_a_2906_ = lean_ctor_get(v___x_2905_, 0);
                    lean_inc(v_a_2906_);
                    lean_dec_ref_known(v___x_2905_, 1);
                    v_fileName_2907_ = lean_ctor_get(v___y_2899_, 0);
                    v_fileMap_2908_ = lean_ctor_get(v___y_2899_, 1);
                    v_currRecDepth_2909_ = lean_ctor_get(v___y_2899_, 2);
                    v_cmdPos_2910_ = lean_ctor_get(v___y_2899_, 3);
                    v_macroStack_2911_ = lean_ctor_get(v___y_2899_, 4);
                    v_quotContext_x3f_2912_ = lean_ctor_get(v___y_2899_, 5);
                    v_currMacroScope_2913_ = lean_ctor_get(v___y_2899_, 6);
                    v_snap_x3f_2914_ = lean_ctor_get(v___y_2899_, 8);
                    v_cancelTk_x3f_2915_ = lean_ctor_get(v___y_2899_, 9);
                    v_suppressElabErrors_2916_ = lean_ctor_get_uint8(
                        v___y_2899_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_2917_ = l_Lean_replaceRef(v_kw_2897_, v_a_2906_);
                    lean_dec(v_a_2906_);
                    lean_dec(v_kw_2897_);
                    lean_inc(v_cancelTk_x3f_2915_);
                    lean_inc(v_snap_x3f_2914_);
                    lean_inc(v_currMacroScope_2913_);
                    lean_inc(v_quotContext_x3f_2912_);
                    lean_inc(v_macroStack_2911_);
                    lean_inc(v_cmdPos_2910_);
                    lean_inc(v_currRecDepth_2909_);
                    lean_inc_ref(v_fileMap_2908_);
                    lean_inc_ref(v_fileName_2907_);
                    v___x_2918_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_2918_, 0, v_fileName_2907_);
                    lean_ctor_set(v___x_2918_, 1, v_fileMap_2908_);
                    lean_ctor_set(v___x_2918_, 2, v_currRecDepth_2909_);
                    lean_ctor_set(v___x_2918_, 3, v_cmdPos_2910_);
                    lean_ctor_set(v___x_2918_, 4, v_macroStack_2911_);
                    lean_ctor_set(v___x_2918_, 5, v_quotContext_x3f_2912_);
                    lean_ctor_set(v___x_2918_, 6, v_currMacroScope_2913_);
                    lean_ctor_set(v___x_2918_, 7, v_ref_2917_);
                    lean_ctor_set(v___x_2918_, 8, v_snap_x3f_2914_);
                    lean_ctor_set(v___x_2918_, 9, v_cancelTk_x3f_2915_);
                    lean_ctor_set_uint8(
                        v___x_2918_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2916_,
                    );
                    v___x_2919_ = l_Lean_Elab_Command_getRef___redArg(v___x_2918_);
                    if lean_obj_tag(v___x_2919_) == 0 {
                        v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
                        lean_inc(v_a_2920_);
                        lean_dec_ref_known(v___x_2919_, 1);
                        v___x_2921_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_2918_);
                        if lean_obj_tag(v___x_2921_) == 0 {
                            v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
                            lean_inc(v_a_2922_);
                            lean_dec_ref_known(v___x_2921_, 1);
                            v___x_2923_ = 0;
                            v___x_2924_ = l_Lean_SourceInfo_fromRef(v_a_2920_, v___x_2923_);
                            lean_dec(v_a_2920_);
                            if lean_obj_tag(v_quotContext_x3f_2912_) == 0 {
                                v___x_2925_ = l_Lean_getMainModule___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__2___redArg(v___y_2903_);
                                v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
                                lean_inc(v_a_2926_);
                                lean_dec_ref(v___x_2925_);
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
                                v_val_2927_ = lean_ctor_get(v_quotContext_x3f_2912_, 0);
                                lean_inc(v_val_2927_);
                                lean_inc_ref(v_quotContext_x3f_2912_);
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
                            lean_dec(v_a_2920_);
                            lean_dec_ref_known(v___x_2918_, 10);
                            lean_dec(v___y_2904_);
                            lean_dec(v___y_2902_);
                            lean_dec(v___y_2901_);
                            lean_dec(v___y_2900_);
                            lean_dec(v_stx_2416_);
                            v_a_2928_ = lean_ctor_get(v___x_2921_, 0);
                            v_isSharedCheck_2935_ = (!lean_is_exclusive(v___x_2921_)) as u8;
                            if v_isSharedCheck_2935_ == 0 {
                                v___x_2930_ = v___x_2921_;
                                v_isShared_2931_ = v_isSharedCheck_2935_;
                                state = 27;
                                continue;
                            } else {
                                lean_inc(v_a_2928_);
                                lean_dec(v___x_2921_);
                                v___x_2930_ = lean_box(0);
                                v_isShared_2931_ = v_isSharedCheck_2935_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v___x_2918_, 10);
                        lean_dec(v___y_2904_);
                        lean_dec(v___y_2902_);
                        lean_dec(v___y_2901_);
                        lean_dec(v___y_2900_);
                        lean_dec(v_stx_2416_);
                        v_a_2936_ = lean_ctor_get(v___x_2919_, 0);
                        v_isSharedCheck_2943_ = (!lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2943_ == 0 {
                            v___x_2938_ = v___x_2919_;
                            v_isShared_2939_ = v_isSharedCheck_2943_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_2936_);
                            lean_dec(v___x_2919_);
                            v___x_2938_ = lean_box(0);
                            v_isShared_2939_ = v_isSharedCheck_2943_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_2904_);
                    lean_dec(v___y_2902_);
                    lean_dec(v___y_2901_);
                    lean_dec(v___y_2900_);
                    lean_dec(v_kw_2897_);
                    lean_dec(v_stx_2416_);
                    v_a_2944_ = lean_ctor_get(v___x_2905_, 0);
                    v_isSharedCheck_2951_ = (!lean_is_exclusive(v___x_2905_)) as u8;
                    if v_isSharedCheck_2951_ == 0 {
                        v___x_2946_ = v___x_2905_;
                        v_isShared_2947_ = v_isSharedCheck_2951_;
                        state = 31;
                        continue;
                    } else {
                        lean_inc(v_a_2944_);
                        lean_dec(v___x_2905_);
                        v___x_2946_ = lean_box(0);
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
                    v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
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
                    v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
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
                    v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
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
                lean_dec(v___x_2493_);
                if lean_obj_tag(v___x_2958_) == 0 {
                    v___x_2959_ = lean_box(0);
                    v___y_2899_ = v___y_2953_;
                    v___y_2900_ = v___y_2954_;
                    v___y_2901_ = v___y_2955_;
                    v___y_2902_ = v___y_2957_;
                    v___y_2903_ = v___y_2956_;
                    v___y_2904_ = v___x_2959_;
                    state = 26;
                    continue;
                } else {
                    v_val_2960_ = lean_ctor_get(v___x_2958_, 0);
                    v_isSharedCheck_2967_ = (!lean_is_exclusive(v___x_2958_)) as u8;
                    if v_isSharedCheck_2967_ == 0 {
                        v___x_2962_ = v___x_2958_;
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_val_2960_);
                        lean_dec(v___x_2958_);
                        v___x_2962_ = lean_box(0);
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
                    v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_val_2960_);
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
                v___x_2972_ = lean_unsigned_to_nat(4);
                v_cfg_2973_ = l_Lean_Syntax_getArg(v_stx_2416_, v___x_2972_);
                v___x_2974_ = l_Lean_Syntax_getOptional_x3f(v___x_2495_);
                lean_dec(v___x_2495_);
                if lean_obj_tag(v___x_2974_) == 0 {
                    v___x_2975_ = lean_box(0);
                    v___y_2953_ = v___y_2970_;
                    v___y_2954_ = v_nameStx_x3f_2969_;
                    v___y_2955_ = v_cfg_2973_;
                    v___y_2956_ = v___y_2971_;
                    v___y_2957_ = v___x_2975_;
                    state = 33;
                    continue;
                } else {
                    v_val_2976_ = lean_ctor_get(v___x_2974_, 0);
                    v_isSharedCheck_2983_ = (!lean_is_exclusive(v___x_2974_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v___x_2978_ = v___x_2974_;
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_val_2976_);
                        lean_dec(v___x_2974_);
                        v___x_2978_ = lean_box(0);
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
                    v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_val_2976_);
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
    mut v_stx_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2997_: *mut LeanObject = core::ptr::null_mut();
    v_res_2997_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand(
        v_stx_2993_,
        v_a_2994_,
        v_a_2995_,
    );
    lean_dec(v_a_2995_);
    lean_dec_ref(v_a_2994_);
    return v_res_2997_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(
    mut v_00_u03b1_2998_: *mut LeanObject,
    mut v_ref_2999_: *mut LeanObject,
    mut v_msg_3000_: *mut LeanObject,
    mut v___y_3001_: *mut LeanObject,
    mut v___y_3002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    v___x_3004_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___redArg(v_ref_2999_, v_msg_3000_, v___y_3001_, v___y_3002_);
    return v___x_3004_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0___boxed(
    mut v_00_u03b1_3005_: *mut LeanObject,
    mut v_ref_3006_: *mut LeanObject,
    mut v_msg_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3011_: *mut LeanObject = core::ptr::null_mut();
    v_res_3011_ = l_Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0(v_00_u03b1_3005_, v_ref_3006_, v_msg_3007_, v___y_3008_, v___y_3009_);
    lean_dec(v___y_3009_);
    lean_dec_ref(v___y_3008_);
    lean_dec(v_ref_3006_);
    return v_res_3011_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(
    mut v_msgData_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    v___x_3016_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___redArg(v_msgData_3012_, v___y_3014_);
    return v___x_3016_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2___boxed(
    mut v_msgData_3017_: *mut LeanObject,
    mut v___y_3018_: *mut LeanObject,
    mut v___y_3019_: *mut LeanObject,
    mut v___y_3020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3021_: *mut LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__2(v_msgData_3017_, v___y_3018_, v___y_3019_);
    lean_dec(v___y_3019_);
    lean_dec_ref(v___y_3018_);
    return v_res_3021_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(
    mut v_00_u03b1_3022_: *mut LeanObject,
    mut v_msg_3023_: *mut LeanObject,
    mut v___y_3024_: *mut LeanObject,
    mut v___y_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    v___x_3027_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___redArg(v_msg_3023_, v___y_3024_, v___y_3025_);
    return v___x_3027_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0___boxed(
    mut v_00_u03b1_3028_: *mut LeanObject,
    mut v_msg_3029_: *mut LeanObject,
    mut v___y_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3033_: *mut LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0(v_00_u03b1_3028_, v_msg_3029_, v___y_3030_, v___y_3031_);
    lean_dec(v___y_3031_);
    lean_dec_ref(v___y_3030_);
    return v_res_3033_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(
    mut v_msgData_3034_: *mut LeanObject,
    mut v_macroStack_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    v___x_3039_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___redArg(v_msgData_3034_, v_macroStack_3035_, v___y_3037_);
    return v___x_3039_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3___boxed(
    mut v_msgData_3040_: *mut LeanObject,
    mut v_macroStack_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
    mut v___y_3044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3045_: *mut LeanObject = core::ptr::null_mut();
    v_res_3045_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__0_spec__0_spec__3(v_msgData_3040_, v_macroStack_3041_, v___y_3042_, v___y_3043_);
    lean_dec(v___y_3043_);
    lean_dec_ref(v___y_3042_);
    return v_res_3045_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1()
-> *mut LeanObject {
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    v___x_3074_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3075_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__12;
    v___x_3076_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1___closed__10;
    v___x_3077_ = lean_alloc_closure(
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
    mut v_a_3079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3080_: *mut LeanObject = core::ptr::null_mut();
    v_res_3080_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
    return v_res_3080_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4()
-> *mut LeanObject {
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    v___x_3088_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__3;
    v___x_3089_ = l_String_toRawSubstring_x27(v___x_3088_);
    return v___x_3089_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7()
-> *mut LeanObject {
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    v___x_3093_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__6;
    v___x_3094_ = l_String_toRawSubstring_x27(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13()
-> *mut LeanObject {
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    v___x_3106_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__12;
    v___x_3107_ = l_String_toRawSubstring_x27(v___x_3106_);
    return v___x_3107_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16()
-> *mut LeanObject {
    let mut v___x_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    v___x_3111_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__15;
    v___x_3112_ = l_String_toRawSubstring_x27(v___x_3111_);
    return v___x_3112_;
}
pub unsafe fn _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22()
-> *mut LeanObject {
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut LeanObject = core::ptr::null_mut();
    v___x_3119_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__21;
    v___x_3120_ = l_String_toRawSubstring_x27(v___x_3119_);
    return v___x_3120_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(
    mut v_stx_3145_: *mut LeanObject,
    mut v_a_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: u8 = 0;
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3329_: u8 = 0;
    let mut v_wds_x3f_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___y_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_x3f_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: u8 = 0;
    let mut v___x_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: u8 = 0;
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: u8 = 0;
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: u8 = 0;
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: u8 = 0;
    let mut v___x_3517_: u8 = 0;
    let mut v___x_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: u8 = 0;
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: u8 = 0;
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wds_x3f_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u8 = 0;
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kw_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: u8 = 0;
    let mut v___x_3559_: u8 = 0;
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pkg_x3f_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: u8 = 0;
    let mut v___x_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: u8 = 0;
    let mut v___x_3580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3171_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1;
                lean_inc(v_stx_3145_);
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
                    lean_dec(v_stx_3145_);
                    return v___x_3193_;
                } else {
                    v___x_3194_ = lean_unsigned_to_nat(0);
                    v___x_3578_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3194_);
                    v___x_3579_ = l_Lean_Syntax_isNone(v___x_3578_);
                    if v___x_3579_ == 0 {
                        v___x_3580_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3578_);
                        v___x_3581_ = l_Lean_Syntax_matchesNull(v___x_3578_, v___x_3580_);
                        if v___x_3581_ == 0 {
                            lean_dec(v___x_3578_);
                            v___x_3582_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                            v___x_3583_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_3145_,
                                v___x_3582_,
                                v_a_3146_,
                                v_a_3147_,
                            );
                            lean_dec(v_stx_3145_);
                            return v___x_3583_;
                        } else {
                            v_doc_x3f_3584_ = l_Lean_Syntax_getArg(v___x_3578_, v___x_3194_);
                            lean_dec(v___x_3578_);
                            v___x_3585_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3585_, 0, v_doc_x3f_3584_);
                            v_doc_x3f_3566_ = v___x_3585_;
                            v___y_3567_ = v_a_3146_;
                            v___y_3568_ = v_a_3147_;
                            state = 13;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_3578_);
                        v___x_3586_ = lean_box(0);
                        v_doc_x3f_3566_ = v___x_3586_;
                        v___y_3567_ = v_a_3146_;
                        v___y_3568_ = v_a_3147_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v___y_3154_);
                v___x_3165_ = l_Array_append___redArg(v___y_3154_, v___y_3164_);
                lean_dec_ref(v___y_3164_);
                lean_inc(v___y_3163_);
                lean_inc_n(v___y_3159_, 3);
                v___x_3166_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3166_, 0, v___y_3159_);
                lean_ctor_set(v___x_3166_, 1, v___y_3163_);
                lean_ctor_set(v___x_3166_, 2, v___x_3165_);
                lean_inc(v___y_3155_);
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
                v___x_3170_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3170_, 0, v___x_3169_);
                lean_ctor_set(v___x_3170_, 1, v___y_3156_);
                return v___x_3170_;
            }
            2 => {
                lean_inc_ref(v___y_3184_);
                v___x_3186_ = l_Array_append___redArg(v___y_3184_, v___y_3185_);
                lean_dec_ref(v___y_3185_);
                lean_inc(v___y_3178_);
                lean_inc_n(v___y_3175_, 2);
                v___x_3187_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3187_, 0, v___y_3175_);
                lean_ctor_set(v___x_3187_, 1, v___y_3178_);
                lean_ctor_set(v___x_3187_, 2, v___x_3186_);
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
                v___x_3190_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3190_, 0, v___x_3189_);
                lean_ctor_set(v___x_3190_, 1, v___y_3179_);
                return v___x_3190_;
            }
            3 => {
                lean_inc_ref_n(v___y_3203_, 2);
                v___x_3217_ = l_Array_append___redArg(v___y_3203_, v___y_3216_);
                lean_dec_ref(v___y_3216_);
                lean_inc_n(v___y_3214_, 8);
                lean_inc_n(v___y_3210_, 41);
                v___x_3218_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3218_, 0, v___y_3210_);
                lean_ctor_set(v___x_3218_, 1, v___y_3214_);
                lean_ctor_set(v___x_3218_, 2, v___x_3217_);
                v___x_3219_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__15;
                lean_inc_ref_n(v___y_3208_, 9);
                lean_inc_ref_n(v___y_3207_, 13);
                lean_inc_ref_n(v___y_3201_, 13);
                v___x_3220_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3219_);
                v___x_3221_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__16;
                v___x_3222_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3222_, 0, v___y_3210_);
                lean_ctor_set(v___x_3222_, 1, v___x_3221_);
                v___x_3223_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__39;
                v___x_3224_ = l_Lean_Syntax_SepArray_ofElems(v___x_3223_, v___y_3211_);
                lean_dec_ref(v___y_3211_);
                v___x_3225_ = l_Array_append___redArg(v___y_3203_, v___x_3224_);
                lean_dec_ref(v___x_3224_);
                v___x_3226_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3226_, 0, v___y_3210_);
                lean_ctor_set(v___x_3226_, 1, v___y_3214_);
                lean_ctor_set(v___x_3226_, 2, v___x_3225_);
                v___x_3227_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__17;
                v___x_3228_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3228_, 0, v___y_3210_);
                lean_ctor_set(v___x_3228_, 1, v___x_3227_);
                v___x_3229_ = l_Lean_Syntax_node3(
                    v___y_3210_,
                    v___x_3220_,
                    v___x_3222_,
                    v___x_3226_,
                    v___x_3228_,
                );
                v___x_3230_ = l_Lean_Syntax_node1(v___y_3210_, v___y_3214_, v___x_3229_);
                lean_inc_n(v___y_3202_, 21);
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
                lean_inc_ref_n(v___y_3200_, 3);
                v___x_3233_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3200_, v___x_3232_);
                v___x_3234_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__6;
                v___x_3235_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3235_, 0, v___y_3210_);
                lean_ctor_set(v___x_3235_, 1, v___x_3234_);
                v___x_3236_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__7;
                v___x_3237_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3200_, v___x_3236_);
                v___x_3238_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__4);
                v___x_3239_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__5;
                lean_inc_n(v___y_3212_, 3);
                lean_inc_n(v___y_3197_, 3);
                v___x_3240_ = l_Lean_addMacroScope(v___y_3197_, v___x_3239_, v___y_3212_);
                lean_inc_n(v___y_3198_, 4);
                v___x_3241_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3241_, 0, v___y_3210_);
                lean_ctor_set(v___x_3241_, 1, v___x_3238_);
                lean_ctor_set(v___x_3241_, 2, v___x_3240_);
                lean_ctor_set(v___x_3241_, 3, v___y_3198_);
                v___x_3242_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3237_, v___x_3241_, v___y_3202_);
                v___x_3243_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__9;
                v___x_3244_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3200_, v___x_3243_);
                v___x_3245_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__11;
                v___x_3246_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3245_);
                v___x_3247_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__12;
                v___x_3248_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3248_, 0, v___y_3210_);
                lean_ctor_set(v___x_3248_, 1, v___x_3247_);
                v___x_3249_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__7);
                v___x_3250_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__8;
                v___x_3251_ = l_Lean_addMacroScope(v___y_3197_, v___x_3250_, v___y_3212_);
                v___x_3252_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__10;
                v___x_3253_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__11;
                v___x_3254_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3254_, 0, v___x_3253_);
                lean_ctor_set(v___x_3254_, 1, v___y_3198_);
                v___x_3255_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3255_, 0, v___x_3252_);
                lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                v___x_3256_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3256_, 0, v___y_3210_);
                lean_ctor_set(v___x_3256_, 1, v___x_3249_);
                lean_ctor_set(v___x_3256_, 2, v___x_3251_);
                lean_ctor_set(v___x_3256_, 3, v___x_3255_);
                v___x_3257_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3246_, v___x_3248_, v___x_3256_);
                v___x_3258_ = l_Lean_Syntax_node1(v___y_3210_, v___y_3214_, v___x_3257_);
                v___x_3259_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3244_, v___y_3202_, v___x_3258_);
                v___x_3260_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38;
                v___x_3261_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3261_, 0, v___y_3210_);
                lean_ctor_set(v___x_3261_, 1, v___x_3260_);
                v___x_3262_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__30;
                v___x_3263_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3262_);
                v___x_3264_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__31;
                v___x_3265_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3265_, 0, v___y_3210_);
                lean_ctor_set(v___x_3265_, 1, v___x_3264_);
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
                v___x_3272_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__13);
                v___x_3273_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__14;
                v___x_3274_ = l_Lean_addMacroScope(v___y_3197_, v___x_3273_, v___y_3212_);
                v___x_3275_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3275_, 0, v___y_3210_);
                lean_ctor_set(v___x_3275_, 1, v___x_3272_);
                lean_ctor_set(v___x_3275_, 2, v___x_3274_);
                lean_ctor_set(v___x_3275_, 3, v___y_3198_);
                lean_inc(v___x_3271_);
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
                v___x_3281_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3281_, 0, v___y_3210_);
                lean_ctor_set(v___x_3281_, 1, v___x_3280_);
                v___x_3282_ = l_Lean_Syntax_node1(v___y_3210_, v___x_3279_, v___x_3281_);
                lean_inc_ref_n(v___x_3261_, 2);
                lean_inc(v___x_3278_);
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
                lean_inc(v___x_3269_);
                v___x_3285_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3269_, v___x_3276_, v___x_3284_);
                v___x_3286_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3286_, 0, v___y_3210_);
                lean_ctor_set(v___x_3286_, 1, v___x_3223_);
                v___x_3287_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__16);
                v___x_3288_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__17;
                v___x_3289_ = l_Lean_addMacroScope(v___y_3197_, v___x_3288_, v___y_3212_);
                v___x_3290_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_3290_, 0, v___y_3210_);
                lean_ctor_set(v___x_3290_, 1, v___x_3287_);
                lean_ctor_set(v___x_3290_, 2, v___x_3289_);
                lean_ctor_set(v___x_3290_, 3, v___y_3198_);
                v___x_3291_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___x_3271_, v___x_3290_, v___y_3202_);
                v___x_3292_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__18;
                v___x_3293_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3292_);
                v___x_3294_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3294_, 0, v___y_3210_);
                lean_ctor_set(v___x_3294_, 1, v___x_3292_);
                v___x_3295_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__19;
                v___x_3296_ =
                    l_Lean_Name_mkStr4(v___y_3201_, v___y_3207_, v___y_3208_, v___x_3295_);
                v___x_3297_ = l_Lean_Syntax_node1(v___y_3210_, v___y_3214_, v___y_3205_);
                v___x_3298_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__20;
                v___x_3299_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3299_, 0, v___y_3210_);
                lean_ctor_set(v___x_3299_, 1, v___x_3298_);
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
                v___x_3311_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3311_, 0, v___y_3210_);
                lean_ctor_set(v___x_3311_, 1, v___x_3310_);
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
                lean_inc(v___y_3209_);
                v___x_3313_ =
                    l_Lean_Syntax_node2(v___y_3210_, v___y_3209_, v___y_3202_, v___y_3202_);
                if lean_obj_tag(v___y_3215_) == 1 {
                    v_val_3314_ = lean_ctor_get(v___y_3215_, 0);
                    lean_inc(v_val_3314_);
                    lean_dec_ref_known(v___y_3215_, 1);
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
                    lean_dec(v___y_3215_);
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
                v_methods_3333_ = lean_ctor_get(v___y_3331_, 0);
                v_quotContext_3334_ = lean_ctor_get(v___y_3331_, 1);
                v_currMacroScope_3335_ = lean_ctor_get(v___y_3331_, 2);
                v_currRecDepth_3336_ = lean_ctor_get(v___y_3331_, 3);
                v_maxRecDepth_3337_ = lean_ctor_get(v___y_3331_, 4);
                v_ref_3338_ = lean_ctor_get(v___y_3331_, 5);
                v_ref_3339_ = l_Lean_replaceRef(v___y_3326_, v_ref_3338_);
                lean_dec(v___y_3326_);
                lean_inc(v_ref_3339_);
                lean_inc(v_maxRecDepth_3337_);
                lean_inc(v_currRecDepth_3336_);
                lean_inc(v_currMacroScope_3335_);
                lean_inc(v_quotContext_3334_);
                lean_inc(v_methods_3333_);
                v___x_3340_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_3340_, 0, v_methods_3333_);
                lean_ctor_set(v___x_3340_, 1, v_quotContext_3334_);
                lean_ctor_set(v___x_3340_, 2, v_currMacroScope_3335_);
                lean_ctor_set(v___x_3340_, 3, v_currRecDepth_3336_);
                lean_ctor_set(v___x_3340_, 4, v_maxRecDepth_3337_);
                lean_ctor_set(v___x_3340_, 5, v_ref_3339_);
                v___x_3341_ =
                    l_Lake_DSL_expandOptSimpleBinder(v___y_3323_, v___x_3340_, v___y_3332_);
                lean_dec_ref_known(v___x_3340_, 6);
                if lean_obj_tag(v___x_3341_) == 0 {
                    v_a_3342_ = lean_ctor_get(v___x_3341_, 0);
                    lean_inc(v_a_3342_);
                    v_a_3343_ = lean_ctor_get(v___x_3341_, 1);
                    lean_inc(v_a_3343_);
                    lean_dec_ref_known(v___x_3341_, 2);
                    v___x_3344_ = l_Lean_SourceInfo_fromRef(v_ref_3339_, v___y_3329_);
                    lean_dec(v_ref_3339_);
                    v___x_3345_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__10;
                    v___x_3346_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__51;
                    lean_inc_ref_n(v___y_3322_, 5);
                    lean_inc_ref_n(v___y_3327_, 5);
                    v___x_3347_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___x_3345_, v___x_3346_);
                    v___x_3348_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__52;
                    v___x_3349_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___x_3345_, v___x_3348_);
                    v___x_3350_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                    v___x_3351_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                    lean_inc_n(v___x_3344_, 5);
                    v___x_3352_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3352_, 0, v___x_3344_);
                    lean_ctor_set(v___x_3352_, 1, v___x_3350_);
                    lean_ctor_set(v___x_3352_, 2, v___x_3351_);
                    lean_inc_ref_n(v___x_3352_, 2);
                    v___x_3353_ = l_Lean_Syntax_node1(v___x_3344_, v___x_3349_, v___x_3352_);
                    v___x_3354_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__57;
                    v___x_3355_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__58;
                    v___x_3356_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___x_3354_, v___x_3355_);
                    v___x_3357_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22), core::ptr::addr_of_mut!(l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22_once), _init_l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__22);
                    v___x_3358_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__24;
                    lean_inc(v_currMacroScope_3335_);
                    lean_inc(v_quotContext_3334_);
                    v___x_3359_ = l_Lean_addMacroScope(
                        v_quotContext_3334_,
                        v___x_3358_,
                        v_currMacroScope_3335_,
                    );
                    v___x_3360_ = lean_box(0);
                    v___x_3361_ = lean_alloc_ctor(3, 4, (0) as u32);
                    lean_ctor_set(v___x_3361_, 0, v___x_3344_);
                    lean_ctor_set(v___x_3361_, 1, v___x_3357_);
                    lean_ctor_set(v___x_3361_, 2, v___x_3359_);
                    lean_ctor_set(v___x_3361_, 3, v___x_3360_);
                    v___x_3362_ =
                        l_Lean_Syntax_node2(v___x_3344_, v___x_3356_, v___x_3361_, v___x_3352_);
                    v___x_3363_ =
                        l_Lean_Syntax_node2(v___x_3344_, v___x_3347_, v___x_3353_, v___x_3362_);
                    v___x_3364_ = lean_mk_empty_array_with_capacity(v___y_3328_);
                    v___x_3365_ = lean_array_push(v___x_3364_, v___x_3363_);
                    v___x_3366_ = l_Lake_DSL_expandAttrs(v___y_3321_);
                    v___x_3367_ = l_Array_append___redArg(v___x_3365_, v___x_3366_);
                    lean_dec_ref(v___x_3366_);
                    v___x_3368_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__0;
                    lean_inc_ref_n(v___y_3324_, 2);
                    v___x_3369_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___y_3324_, v___x_3368_);
                    v___x_3370_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__1;
                    v___x_3371_ =
                        l_Lean_Name_mkStr4(v___y_3327_, v___y_3322_, v___y_3324_, v___x_3370_);
                    if lean_obj_tag(v___y_3318_) == 1 {
                        v_val_3372_ = lean_ctor_get(v___y_3318_, 0);
                        lean_inc(v_val_3372_);
                        lean_dec_ref_known(v___y_3318_, 1);
                        v___x_3373_ = l_Array_mkArray1___redArg(v_val_3372_);
                        lean_inc(v_currMacroScope_3335_);
                        lean_inc(v_quotContext_3334_);
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
                        lean_dec(v___y_3318_);
                        v___x_3374_ = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__29;
                        lean_inc(v_currMacroScope_3335_);
                        lean_inc(v_quotContext_3334_);
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
                    lean_dec(v_ref_3339_);
                    lean_dec(v_wds_x3f_3330_);
                    lean_dec(v___y_3321_);
                    lean_dec(v___y_3319_);
                    lean_dec(v___y_3318_);
                    v_a_3375_ = lean_ctor_get(v___x_3341_, 0);
                    v_a_3376_ = lean_ctor_get(v___x_3341_, 1);
                    v_isSharedCheck_3383_ = (!lean_is_exclusive(v___x_3341_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3378_ = v___x_3341_;
                        v_isShared_3379_ = v_isSharedCheck_3383_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3376_);
                        lean_inc(v_a_3375_);
                        lean_dec(v___x_3341_);
                        v___x_3378_ = lean_box(0);
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
                    v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3375_);
                    lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_a_3376_);
                    v___x_3381_ = v_reuseFailAlloc_3382_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3381_;
            }
            7 => {
                lean_inc_ref_n(v___y_3397_, 2);
                v___x_3399_ = l_Array_append___redArg(v___y_3397_, v___y_3398_);
                lean_dec_ref(v___y_3398_);
                lean_inc_n(v___y_3389_, 2);
                lean_inc_n(v___y_3385_, 6);
                v___x_3400_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3400_, 0, v___y_3385_);
                lean_ctor_set(v___x_3400_, 1, v___y_3389_);
                lean_ctor_set(v___x_3400_, 2, v___x_3399_);
                v___x_3401_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                v___x_3402_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__25;
                lean_inc_ref_n(v___y_3388_, 2);
                lean_inc_ref_n(v___y_3390_, 2);
                v___x_3403_ =
                    l_Lean_Name_mkStr4(v___y_3390_, v___y_3388_, v___x_3401_, v___x_3402_);
                v___x_3404_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__38;
                v___x_3405_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3405_, 0, v___y_3385_);
                lean_ctor_set(v___x_3405_, 1, v___x_3404_);
                lean_inc_ref(v___y_3386_);
                v___x_3406_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3406_, 0, v___y_3385_);
                lean_ctor_set(v___x_3406_, 1, v___y_3386_);
                lean_inc(v___y_3394_);
                v___x_3407_ =
                    l_Lean_Syntax_node2(v___y_3385_, v___y_3394_, v___x_3406_, v___y_3393_);
                v___x_3408_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__26;
                v___x_3409_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___closed__27;
                v___x_3410_ =
                    l_Lean_Name_mkStr4(v___y_3390_, v___y_3388_, v___x_3408_, v___x_3409_);
                v___x_3411_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3411_, 0, v___y_3385_);
                lean_ctor_set(v___x_3411_, 1, v___y_3389_);
                lean_ctor_set(v___x_3411_, 2, v___y_3397_);
                lean_inc_ref(v___x_3411_);
                v___x_3412_ =
                    l_Lean_Syntax_node2(v___y_3385_, v___x_3410_, v___x_3411_, v___x_3411_);
                if lean_obj_tag(v___y_3391_) == 1 {
                    v_val_3413_ = lean_ctor_get(v___y_3391_, 0);
                    lean_inc(v_val_3413_);
                    lean_dec_ref_known(v___y_3391_, 1);
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
                    lean_dec(v___y_3391_);
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
                lean_inc_ref(v___y_3429_);
                v___x_3431_ = l_Array_append___redArg(v___y_3429_, v___y_3430_);
                lean_dec_ref(v___y_3430_);
                lean_inc(v___y_3422_);
                lean_inc(v___y_3417_);
                v___x_3432_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3432_, 0, v___y_3417_);
                lean_ctor_set(v___x_3432_, 1, v___y_3422_);
                lean_ctor_set(v___x_3432_, 2, v___x_3431_);
                v___x_3433_ = l_Lean_SourceInfo_fromRef(v___y_3424_, v___x_3191_);
                lean_dec(v___y_3424_);
                v___x_3434_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__23;
                v___x_3435_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3435_, 0, v___x_3433_);
                lean_ctor_set(v___x_3435_, 1, v___x_3434_);
                if lean_obj_tag(v___y_3418_) == 1 {
                    v_val_3436_ = lean_ctor_get(v___y_3418_, 0);
                    lean_inc(v_val_3436_);
                    lean_dec_ref_known(v___y_3418_, 1);
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
                    lean_dec(v___y_3418_);
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
                lean_inc_ref(v___y_3452_);
                v___x_3454_ = l_Array_append___redArg(v___y_3452_, v___y_3453_);
                lean_dec_ref(v___y_3453_);
                lean_inc(v___y_3445_);
                lean_inc(v___y_3440_);
                v___x_3455_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_3455_, 0, v___y_3440_);
                lean_ctor_set(v___x_3455_, 1, v___y_3445_);
                lean_ctor_set(v___x_3455_, 2, v___x_3454_);
                if lean_obj_tag(v___y_3443_) == 1 {
                    v_val_3456_ = lean_ctor_get(v___y_3443_, 0);
                    lean_inc(v_val_3456_);
                    lean_dec_ref_known(v___y_3443_, 1);
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
                    lean_dec(v___y_3443_);
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
                v_ref_3472_ = lean_ctor_get(v___y_3470_, 5);
                v___x_3473_ = 0;
                v___x_3474_ = l_Lean_SourceInfo_fromRef(v_ref_3472_, v___x_3473_);
                v___x_3475_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__3;
                v___x_3476_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4), core::ptr::addr_of_mut!(l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4_once), _init_l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__4);
                if lean_obj_tag(v___y_3460_) == 1 {
                    v_val_3477_ = lean_ctor_get(v___y_3460_, 0);
                    lean_inc(v_val_3477_);
                    lean_dec_ref_known(v___y_3460_, 1);
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
                    lean_dec(v___y_3460_);
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
                v___x_3490_ = lean_unsigned_to_nat(4);
                v___x_3491_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3490_);
                v___x_3492_ =
                    l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__26;
                lean_inc(v___x_3491_);
                v___x_3493_ = l_Lean_Syntax_isOfKind(v___x_3491_, v___x_3492_);
                if v___x_3493_ == 0 {
                    v___x_3494_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__14;
                    v___x_3495_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__15;
                    v___x_3496_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__16;
                    v___x_3497_ =
                        l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__27;
                    lean_inc(v___x_3491_);
                    v___x_3498_ = l_Lean_Syntax_isOfKind(v___x_3491_, v___x_3497_);
                    if v___x_3498_ == 0 {
                        lean_dec(v___x_3491_);
                        lean_dec(v_pkg_x3f_3487_);
                        lean_dec(v___y_3483_);
                        lean_dec(v___y_3482_);
                        lean_dec(v___y_3481_);
                        v___x_3499_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3500_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3499_,
                            v___y_3488_,
                            v___y_3489_,
                        );
                        lean_dec(v_stx_3145_);
                        return v___x_3500_;
                    } else {
                        v___x_3501_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3485_);
                        v___x_3502_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__28;
                        lean_inc(v___x_3501_);
                        v___x_3503_ = l_Lean_Syntax_isOfKind(v___x_3501_, v___x_3502_);
                        if v___x_3503_ == 0 {
                            lean_dec(v___x_3501_);
                            lean_dec(v___x_3491_);
                            lean_dec(v_pkg_x3f_3487_);
                            lean_dec(v___y_3483_);
                            lean_dec(v___y_3482_);
                            lean_dec(v___y_3481_);
                            v___x_3504_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                            v___x_3505_ = l_Lean_Macro_throwErrorAt___redArg(
                                v_stx_3145_,
                                v___x_3504_,
                                v___y_3488_,
                                v___y_3489_,
                            );
                            lean_dec(v_stx_3145_);
                            return v___x_3505_;
                        } else {
                            v___x_3506_ = l_Lean_Syntax_getArg(v___x_3501_, v___x_3194_);
                            v___x_3507_ = l_Lean_Syntax_matchesNull(v___x_3506_, v___x_3194_);
                            if v___x_3507_ == 0 {
                                lean_dec(v___x_3501_);
                                lean_dec(v___x_3491_);
                                lean_dec(v_pkg_x3f_3487_);
                                lean_dec(v___y_3483_);
                                lean_dec(v___y_3482_);
                                lean_dec(v___y_3481_);
                                v___x_3508_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                v___x_3509_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3145_,
                                    v___x_3508_,
                                    v___y_3488_,
                                    v___y_3489_,
                                );
                                lean_dec(v_stx_3145_);
                                return v___x_3509_;
                            } else {
                                v___x_3510_ = l_Lean_Syntax_getArg(v___x_3501_, v___y_3486_);
                                lean_dec(v___x_3501_);
                                v___x_3511_ = l_Lean_Syntax_matchesNull(v___x_3510_, v___x_3194_);
                                if v___x_3511_ == 0 {
                                    lean_dec(v___x_3491_);
                                    lean_dec(v_pkg_x3f_3487_);
                                    lean_dec(v___y_3483_);
                                    lean_dec(v___y_3482_);
                                    lean_dec(v___y_3481_);
                                    v___x_3512_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                    v___x_3513_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_stx_3145_,
                                        v___x_3512_,
                                        v___y_3488_,
                                        v___y_3489_,
                                    );
                                    lean_dec(v_stx_3145_);
                                    return v___x_3513_;
                                } else {
                                    v___x_3514_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3486_);
                                    v___x_3515_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3484_);
                                    lean_dec(v___x_3491_);
                                    v___x_3516_ = l_Lean_Syntax_isNone(v___x_3515_);
                                    if v___x_3516_ == 0 {
                                        lean_inc(v___x_3515_);
                                        v___x_3517_ =
                                            l_Lean_Syntax_matchesNull(v___x_3515_, v___y_3486_);
                                        if v___x_3517_ == 0 {
                                            lean_dec(v___x_3515_);
                                            lean_dec(v___x_3514_);
                                            lean_dec(v_pkg_x3f_3487_);
                                            lean_dec(v___y_3483_);
                                            lean_dec(v___y_3482_);
                                            lean_dec(v___y_3481_);
                                            v___x_3518_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                            v___x_3519_ = l_Lean_Macro_throwErrorAt___redArg(
                                                v_stx_3145_,
                                                v___x_3518_,
                                                v___y_3488_,
                                                v___y_3489_,
                                            );
                                            lean_dec(v_stx_3145_);
                                            return v___x_3519_;
                                        } else {
                                            v_wds_x3f_3520_ =
                                                l_Lean_Syntax_getArg(v___x_3515_, v___x_3194_);
                                            lean_dec(v___x_3515_);
                                            v___x_3521_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                            lean_inc(v_wds_x3f_3520_);
                                            v___x_3522_ = l_Lean_Syntax_isOfKind(
                                                v_wds_x3f_3520_,
                                                v___x_3521_,
                                            );
                                            if v___x_3522_ == 0 {
                                                lean_dec(v_wds_x3f_3520_);
                                                lean_dec(v___x_3514_);
                                                lean_dec(v_pkg_x3f_3487_);
                                                lean_dec(v___y_3483_);
                                                lean_dec(v___y_3482_);
                                                lean_dec(v___y_3481_);
                                                v___x_3523_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                                v___x_3524_ = l_Lean_Macro_throwErrorAt___redArg(
                                                    v_stx_3145_,
                                                    v___x_3523_,
                                                    v___y_3488_,
                                                    v___y_3489_,
                                                );
                                                lean_dec(v_stx_3145_);
                                                return v___x_3524_;
                                            } else {
                                                lean_dec(v_stx_3145_);
                                                v___x_3525_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_3525_, 0, v_wds_x3f_3520_);
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
                                        lean_dec(v___x_3515_);
                                        lean_dec(v_stx_3145_);
                                        v___x_3526_ = lean_box(0);
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
                    lean_inc(v___x_3527_);
                    v___x_3532_ = l_Lean_Syntax_isOfKind(v___x_3527_, v___x_3531_);
                    if v___x_3532_ == 0 {
                        lean_dec(v___x_3527_);
                        lean_dec(v___x_3491_);
                        lean_dec(v_pkg_x3f_3487_);
                        lean_dec(v___y_3483_);
                        lean_dec(v___y_3482_);
                        lean_dec(v___y_3481_);
                        v___x_3533_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3534_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3533_,
                            v___y_3488_,
                            v___y_3489_,
                        );
                        lean_dec(v_stx_3145_);
                        return v___x_3534_;
                    } else {
                        v___x_3535_ = l_Lean_Syntax_getArg(v___x_3527_, v___y_3486_);
                        lean_dec(v___x_3527_);
                        v___x_3536_ = l_Lean_Syntax_getArg(v___x_3491_, v___y_3486_);
                        lean_dec(v___x_3491_);
                        v___x_3537_ = l_Lean_Syntax_isNone(v___x_3536_);
                        if v___x_3537_ == 0 {
                            lean_inc(v___x_3536_);
                            v___x_3538_ = l_Lean_Syntax_matchesNull(v___x_3536_, v___y_3486_);
                            if v___x_3538_ == 0 {
                                lean_dec(v___x_3536_);
                                lean_dec(v___x_3535_);
                                lean_dec(v_pkg_x3f_3487_);
                                lean_dec(v___y_3483_);
                                lean_dec(v___y_3482_);
                                lean_dec(v___y_3481_);
                                v___x_3539_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                v___x_3540_ = l_Lean_Macro_throwErrorAt___redArg(
                                    v_stx_3145_,
                                    v___x_3539_,
                                    v___y_3488_,
                                    v___y_3489_,
                                );
                                lean_dec(v_stx_3145_);
                                return v___x_3540_;
                            } else {
                                v_wds_x3f_3541_ = l_Lean_Syntax_getArg(v___x_3536_, v___x_3194_);
                                lean_dec(v___x_3536_);
                                v___x_3542_ = l_Lake_DSL_elabConfig___at___00__private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand_spec__1___closed__34;
                                lean_inc(v_wds_x3f_3541_);
                                v___x_3543_ = l_Lean_Syntax_isOfKind(v_wds_x3f_3541_, v___x_3542_);
                                if v___x_3543_ == 0 {
                                    lean_dec(v_wds_x3f_3541_);
                                    lean_dec(v___x_3535_);
                                    lean_dec(v_pkg_x3f_3487_);
                                    lean_dec(v___y_3483_);
                                    lean_dec(v___y_3482_);
                                    lean_dec(v___y_3481_);
                                    v___x_3544_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                                    v___x_3545_ = l_Lean_Macro_throwErrorAt___redArg(
                                        v_stx_3145_,
                                        v___x_3544_,
                                        v___y_3488_,
                                        v___y_3489_,
                                    );
                                    lean_dec(v_stx_3145_);
                                    return v___x_3545_;
                                } else {
                                    lean_dec(v_stx_3145_);
                                    v___x_3546_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_3546_, 0, v_wds_x3f_3541_);
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
                            lean_dec(v___x_3536_);
                            lean_dec(v_stx_3145_);
                            v___x_3547_ = lean_box(0);
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
                v___x_3554_ = lean_unsigned_to_nat(2);
                v_kw_3555_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3554_);
                v___x_3556_ = lean_unsigned_to_nat(3);
                v___x_3557_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3556_);
                v___x_3558_ = l_Lean_Syntax_isNone(v___x_3557_);
                if v___x_3558_ == 0 {
                    lean_inc(v___x_3557_);
                    v___x_3559_ = l_Lean_Syntax_matchesNull(v___x_3557_, v___y_3550_);
                    if v___x_3559_ == 0 {
                        lean_dec(v___x_3557_);
                        lean_dec(v_kw_3555_);
                        lean_dec(v_attrs_x3f_3551_);
                        lean_dec(v___y_3549_);
                        v___x_3560_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3561_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3560_,
                            v___y_3552_,
                            v___y_3553_,
                        );
                        lean_dec(v_stx_3145_);
                        return v___x_3561_;
                    } else {
                        v_pkg_x3f_3562_ = l_Lean_Syntax_getArg(v___x_3557_, v___x_3194_);
                        lean_dec(v___x_3557_);
                        v___x_3563_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3563_, 0, v_pkg_x3f_3562_);
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
                    lean_dec(v___x_3557_);
                    v___x_3564_ = lean_box(0);
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
                v___x_3569_ = lean_unsigned_to_nat(1);
                v___x_3570_ = l_Lean_Syntax_getArg(v_stx_3145_, v___x_3569_);
                v___x_3571_ = l_Lean_Syntax_isNone(v___x_3570_);
                if v___x_3571_ == 0 {
                    lean_inc(v___x_3570_);
                    v___x_3572_ = l_Lean_Syntax_matchesNull(v___x_3570_, v___x_3569_);
                    if v___x_3572_ == 0 {
                        lean_dec(v___x_3570_);
                        lean_dec(v_doc_x3f_3566_);
                        v___x_3573_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__2;
                        v___x_3574_ = l_Lean_Macro_throwErrorAt___redArg(
                            v_stx_3145_,
                            v___x_3573_,
                            v___y_3567_,
                            v___y_3568_,
                        );
                        lean_dec(v_stx_3145_);
                        return v___x_3574_;
                    } else {
                        v_attrs_x3f_3575_ = l_Lean_Syntax_getArg(v___x_3570_, v___x_3194_);
                        lean_dec(v___x_3570_);
                        v___x_3576_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3576_, 0, v_attrs_x3f_3575_);
                        v___y_3549_ = v_doc_x3f_3566_;
                        v___y_3550_ = v___x_3569_;
                        v_attrs_x3f_3551_ = v___x_3576_;
                        v___y_3552_ = v___y_3567_;
                        v___y_3553_ = v___y_3568_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3570_);
                    v___x_3577_ = lean_box(0);
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
    mut v_stx_3587_: *mut LeanObject,
    mut v_a_3588_: *mut LeanObject,
    mut v_a_3589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3590_: *mut LeanObject = core::ptr::null_mut();
    v_res_3590_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl(
        v_stx_3587_,
        v_a_3588_,
        v_a_3589_,
    );
    lean_dec_ref(v_a_3588_);
    return v_res_3590_;
}
pub unsafe fn l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1()
-> *mut LeanObject {
    let mut v___x_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    v___x_3596_ = l_Lean_Elab_macroAttribute;
    v___x_3597_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___closed__1;
    v___x_3598_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1___closed__1;
    v___x_3599_ = lean_alloc_closure(
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
    mut v_a_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3602_: *mut LeanObject = core::ptr::null_mut();
    v_res_3602_ = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
    return v_res_3602_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_DSL_Package(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_elabPackageCommand__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl___regBuiltin___private_Lake_DSL_Package_0__Lake_DSL_expandPostUpdateDecl__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_DSL_Package(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_DSL_Package(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_DSL_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_Config_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lake_DSL_Extensions(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_DSL_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_DSL_Package(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_DSL_Package(builtin);
}
