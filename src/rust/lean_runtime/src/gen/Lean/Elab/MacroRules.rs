// Lean compiler output
// Module: Lean.Elab.MacroRules
// Imports: Lean.Elab.Syntax Lean.Elab.AuxDef
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_TSepArray_getElems___redArg,
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getId, l_Lean_mkIdentFrom, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray5___redArg, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node6, l_Lean_addMacroScope, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::l_Lean_Syntax_setArg;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::AuxDef::{
    initialize_Lean_Elab_AuxDef, runtime_initialize_Lean_Elab_AuxDef,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_adaptExpander, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Parser_Command_visibility_ofAttrKind,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Syntax::{
    initialize_Lean_Elab_Syntax, l_Lean_Elab_Command_checkRuleKind,
    l_Lean_Elab_Command_expandNoKindMacroRulesAux, l_Lean_Elab_Command_resolveSyntaxKind,
    runtime_initialize_Lean_Elab_Syntax,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_header, l_Lean_Environment_setExporting};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_getQuotContent, l_Lean_Syntax_isQuot};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0_value: crate::leanh::LeanStringObject<61> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value) as *mut crate::leanh::LeanObject,11985596712582660667 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16_value: crate::leanh::LeanStringObject<63> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [109, 97, 99, 114, 111, 82, 117, 108, 101, 115, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value)
            as *mut crate::leanh::LeanObject,
        3631122813654456582 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value: crate::leanh::LeanStringObject<
    6,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [77, 97, 99, 114, 111, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value)
            as *mut crate::leanh::LeanObject,
        14665357199263665561 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value:
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value:
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value:
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
    m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value:
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
    m_data: [104, 111, 108, 101, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value:
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
    m_data: [95, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value:
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
        110, 111, 69, 114, 114, 111, 114, 73, 102, 85, 110, 117, 115, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value:
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
        110, 111, 95, 101, 114, 114, 111, 114, 95, 105, 102, 95, 117, 110, 117, 115, 101, 100, 37,
        0,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value:
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
    m_data: [97, 112, 112, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value:
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
    m_data: [116, 104, 114, 111, 119, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value)
            as *mut crate::leanh::LeanObject,
        8214547835296698684 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value:
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
    m_data: [77, 111, 110, 97, 100, 69, 120, 99, 101, 112, 116, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value)
            as *mut crate::leanh::LeanObject,
        8171668748642392738 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value)
            as *mut crate::leanh::LeanObject,
        3883738120033471353 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__24_value: crate::leanh::LeanCtorObject<
    2,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 77, 97, 99, 114, 111, 46, 69, 120, 99, 101, 112, 116, 105, 111, 110,
        46, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 83, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value:
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
    m_data: [69, 120, 99, 101, 112, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 83, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value:
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
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value:
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
    m_data: [97, 117, 120, 95, 100, 101, 102, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
            as *mut crate::leanh::LeanObject,
        16981400742628996529 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value)
            as *mut crate::leanh::LeanObject,
        6797826372810318163 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value:
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value)
            as *mut crate::leanh::LeanObject,
        7499624980761693169 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value:
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value:
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
    m_data: [109, 97, 99, 114, 111, 0],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value)
            as *mut crate::leanh::LeanObject,
        5370970300127562257 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value:
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0_value:
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1_value:
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
    m_data: [107, 105, 110, 100, 0],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2_value:
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value:
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
    m_data: [109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 0],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value)
            as *mut crate::leanh::LeanObject,
        127604530719969405 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value)
            as *mut crate::leanh::LeanObject,
        18105168627502861736 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value:
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value:
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value)
            as *mut crate::leanh::LeanObject,
        7983999284776576032 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value)
            as *mut crate::leanh::LeanObject,
        13242179749370575553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value:
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
    m_data: [108, 111, 99, 97, 108, 0],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value)
            as *mut crate::leanh::LeanObject,
        312453245906544776 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value:
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
    m_data: [105, 100, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2533412339571800130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value:
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
    m_data: [100, 111, 99, 67, 111, 109, 109, 101, 110, 116, 0],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value)
            as *mut crate::leanh::LeanObject,
        9063780239635860524 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___closed__0_value: crate::leanh::LeanClosureObject<
    0,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Command_elabMacroRules___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Command_elabMacroRules___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 77, 97, 99, 114, 111, 82, 117, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value) as *mut crate::leanh::LeanObject,11551791596232990586 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 38 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 42 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 56 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = crate::leanh::lean_box(0);
    v___x_1557_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1558_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1557_);
    crate::leanh::lean_ctor_set(v___x_1558_, 1, v___x_1556_);
    return v___x_1558_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1560_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0);
    v___x_1561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___boxed(
    mut v___y_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
    return v_res_1563_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(
    mut v_00_u03b1_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
    mut v___y_1566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
    return v___x_1568_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(
    mut v_00_u03b1_1569_: *mut crate::leanh::LeanObject,
    mut v___y_1570_: *mut crate::leanh::LeanObject,
    mut v___y_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1573_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(
            v_00_u03b1_1569_,
            v___y_1570_,
            v___y_1571_,
        );
    crate::leanh::lean_dec(v___y_1571_);
    crate::leanh::lean_dec_ref(v___y_1570_);
    return v_res_1573_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(
    mut v___y_1574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_st_ref_get(v___y_1574_);
    v_env_1577_ = crate::leanh::lean_ctor_get(v___x_1576_, 0);
    crate::leanh::lean_inc_ref(v_env_1577_);
    crate::leanh::lean_dec(v___x_1576_);
    v___x_1578_ = l_Lean_Environment_header(v_env_1577_);
    crate::leanh::lean_dec_ref(v_env_1577_);
    v_mainModule_1579_ = crate::leanh::lean_ctor_get(v___x_1578_, 0);
    crate::leanh::lean_inc(v_mainModule_1579_);
    crate::leanh::lean_dec_ref(v___x_1578_);
    v___x_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1580_, 0, v_mainModule_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg___boxed(
    mut v___y_1581_: *mut crate::leanh::LeanObject,
    mut v___y_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1583_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(
            v___y_1581_,
        );
    crate::leanh::lean_dec(v___y_1581_);
    return v_res_1583_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(
    mut v___y_1584_: *mut crate::leanh::LeanObject,
    mut v___y_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1587_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(
            v___y_1585_,
        );
    return v___x_1587_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___boxed(
    mut v___y_1588_: *mut crate::leanh::LeanObject,
    mut v___y_1589_: *mut crate::leanh::LeanObject,
    mut v___y_1590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(
        v___y_1588_,
        v___y_1589_,
    );
    crate::leanh::lean_dec(v___y_1589_);
    crate::leanh::lean_dec_ref(v___y_1588_);
    return v_res_1591_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1592_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1592_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1593_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_1594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1594_, 0, v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1595_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_1596_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1597_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1597_, 0, v___x_1596_);
    crate::leanh::lean_ctor_set(v___x_1597_, 1, v___x_1596_);
    crate::leanh::lean_ctor_set(v___x_1597_, 2, v___x_1596_);
    crate::leanh::lean_ctor_set(v___x_1597_, 3, v___x_1596_);
    crate::leanh::lean_ctor_set(v___x_1597_, 4, v___x_1595_);
    crate::leanh::lean_ctor_set(v___x_1597_, 5, v___x_1595_);
    crate::leanh::lean_ctor_set(v___x_1597_, 6, v___x_1595_);
    crate::leanh::lean_ctor_set(v___x_1597_, 7, v___x_1595_);
    crate::leanh::lean_ctor_set(v___x_1597_, 8, v___x_1595_);
    crate::leanh::lean_ctor_set(v___x_1597_, 9, v___x_1595_);
    return v___x_1597_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1599_ = lean_mk_empty_array_with_capacity(v___x_1598_);
    v___x_1600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1600_, 0, v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = 5usize;
    v___x_1602_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1603_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1604_ = lean_mk_empty_array_with_capacity(v___x_1603_);
    v___x_1605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3);
    v___x_1606_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1606_, 0, v___x_1605_);
    crate::leanh::lean_ctor_set(v___x_1606_, 1, v___x_1604_);
    crate::leanh::lean_ctor_set(v___x_1606_, 2, v___x_1602_);
    crate::leanh::lean_ctor_set(v___x_1606_, 3, v___x_1602_);
    crate::leanh::lean_ctor_set_usize(v___x_1606_, 4, v___x_1601_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1607_ = crate::leanh::lean_box(1);
    v___x_1608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4);
    v___x_1609_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_1610_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    crate::leanh::lean_ctor_set(v___x_1610_, 1, v___x_1608_);
    crate::leanh::lean_ctor_set(v___x_1610_, 2, v___x_1607_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_1611_: *mut crate::leanh::LeanObject,
    mut v___y_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = lean_st_ref_get(v___y_1612_);
    v_env_1615_ = crate::leanh::lean_ctor_get(v___x_1614_, 0);
    crate::leanh::lean_inc_ref(v_env_1615_);
    crate::leanh::lean_dec(v___x_1614_);
    v___x_1616_ = lean_st_ref_get(v___y_1612_);
    v_scopes_1617_ = crate::leanh::lean_ctor_get(v___x_1616_, 2);
    crate::leanh::lean_inc(v_scopes_1617_);
    crate::leanh::lean_dec(v___x_1616_);
    v___x_1618_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1619_ = l_List_head_x21___redArg(v___x_1618_, v_scopes_1617_);
    crate::leanh::lean_dec(v_scopes_1617_);
    v_opts_1620_ = crate::leanh::lean_ctor_get(v___x_1619_, 1);
    crate::leanh::lean_inc_ref(v_opts_1620_);
    crate::leanh::lean_dec(v___x_1619_);
    v___x_1621_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2);
    v___x_1622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5);
    v___x_1623_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1623_, 0, v_env_1615_);
    crate::leanh::lean_ctor_set(v___x_1623_, 1, v___x_1621_);
    crate::leanh::lean_ctor_set(v___x_1623_, 2, v___x_1622_);
    crate::leanh::lean_ctor_set(v___x_1623_, 3, v_opts_1620_);
    v___x_1624_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1624_, 0, v___x_1623_);
    crate::leanh::lean_ctor_set(v___x_1624_, 1, v_msgData_1611_);
    v___x_1625_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1625_, 0, v___x_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
    mut v___y_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_1626_, v___y_1627_);
    crate::leanh::lean_dec(v___y_1627_);
    return v_res_1629_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1630_ = crate::leanh::lean_box(1);
    v___x_1631_ = l_Lean_MessageData_ofFormat(v___x_1630_);
    return v___x_1631_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2;
    v___x_1636_ = l_Lean_MessageData_ofFormat(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(
    mut v_x_1637_: *mut crate::leanh::LeanObject,
    mut v_x_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v_before_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v_unused_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1638_) == 0 {
                    return v_x_1637_;
                } else {
                    v_head_1639_ = crate::leanh::lean_ctor_get(v_x_1638_, 0);
                    v_tail_1640_ = crate::leanh::lean_ctor_get(v_x_1638_, 1);
                    v_isSharedCheck_1662_ = (!crate::leanh::lean_is_exclusive(v_x_1638_)) as u8;
                    if v_isSharedCheck_1662_ == 0 {
                        v___x_1642_ = v_x_1638_;
                        v_isShared_1643_ = v_isSharedCheck_1662_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1640_);
                        crate::leanh::lean_inc(v_head_1639_);
                        crate::leanh::lean_dec(v_x_1638_);
                        v___x_1642_ = crate::leanh::lean_box(0);
                        v_isShared_1643_ = v_isSharedCheck_1662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1644_ = crate::leanh::lean_ctor_get(v_head_1639_, 0);
                v_isSharedCheck_1660_ = (!crate::leanh::lean_is_exclusive(v_head_1639_)) as u8;
                if v_isSharedCheck_1660_ == 0 {
                    v_unused_1661_ = crate::leanh::lean_ctor_get(v_head_1639_, 1);
                    crate::leanh::lean_dec(v_unused_1661_);
                    v___x_1646_ = v_head_1639_;
                    v_isShared_1647_ = v_isSharedCheck_1660_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1644_);
                    crate::leanh::lean_dec(v_head_1639_);
                    v___x_1646_ = crate::leanh::lean_box(0);
                    v_isShared_1647_ = v_isSharedCheck_1660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1648_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
                if v_isShared_1647_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1646_, 7);
                    crate::leanh::lean_ctor_set(v___x_1646_, 1, v___x_1648_);
                    crate::leanh::lean_ctor_set(v___x_1646_, 0, v_x_1637_);
                    v___x_1650_ = v___x_1646_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_x_1637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1651_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3);
                if v_isShared_1643_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1642_, 7);
                    crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1651_);
                    crate::leanh::lean_ctor_set(v___x_1642_, 0, v___x_1650_);
                    v___x_1653_ = v___x_1642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1651_);
                    v___x_1653_ = v_reuseFailAlloc_1658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1654_ = l_Lean_MessageData_ofSyntax(v_before_1644_);
                v___x_1655_ = l_Lean_indentD(v___x_1654_);
                v___x_1656_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1656_, 0, v___x_1653_);
                crate::leanh::lean_ctor_set(v___x_1656_, 1, v___x_1655_);
                v_x_1637_ = v___x_1656_;
                v_x_1638_ = v_tail_1640_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(
    mut v_opts_1663_: *mut crate::leanh::LeanObject,
    mut v_opt_1664_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1665_ = crate::leanh::lean_ctor_get(v_opt_1664_, 0);
    v_defValue_1666_ = crate::leanh::lean_ctor_get(v_opt_1664_, 1);
    v_map_1667_ = crate::leanh::lean_ctor_get(v_opts_1663_, 0);
    v___x_1668_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1667_,
            v_name_1665_,
        );
    if crate::leanh::lean_obj_tag(v___x_1668_) == 0 {
        let mut v___x_1669_: u8 = 0;
        v___x_1669_ = (crate::leanh::lean_unbox(v_defValue_1666_) as u8);
        return v___x_1669_;
    } else {
        let mut v_val_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1670_ = crate::leanh::lean_ctor_get(v___x_1668_, 0);
        crate::leanh::lean_inc(v_val_1670_);
        crate::leanh::lean_dec_ref_known(v___x_1668_, 1);
        if crate::leanh::lean_obj_tag(v_val_1670_) == 1 {
            let mut v_v_1671_: u8 = 0;
            v_v_1671_ = crate::leanh::lean_ctor_get_uint8(v_val_1670_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1670_, 0);
            return v_v_1671_;
        } else {
            let mut v___x_1672_: u8 = 0;
            crate::leanh::lean_dec(v_val_1670_);
            v___x_1672_ = (crate::leanh::lean_unbox(v_defValue_1666_) as u8);
            return v___x_1672_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(
    mut v_opts_1673_: *mut crate::leanh::LeanObject,
    mut v_opt_1674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1675_: u8 = 0;
    let mut v_r_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_1673_, v_opt_1674_);
    crate::leanh::lean_dec_ref(v_opt_1674_);
    crate::leanh::lean_dec_ref(v_opts_1673_);
    v_r_1676_ = crate::leanh::lean_box((v_res_1675_) as usize);
    return v_r_1676_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1680_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1;
    v___x_1681_ = l_Lean_MessageData_ofFormat(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(
    mut v_msgData_1682_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_unused_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1686_ = lean_st_ref_get(v___y_1684_);
                v_scopes_1687_ = crate::leanh::lean_ctor_get(v___x_1686_, 2);
                crate::leanh::lean_inc(v_scopes_1687_);
                crate::leanh::lean_dec(v___x_1686_);
                v___x_1688_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1689_ = l_List_head_x21___redArg(v___x_1688_, v_scopes_1687_);
                crate::leanh::lean_dec(v_scopes_1687_);
                v_opts_1690_ = crate::leanh::lean_ctor_get(v___x_1689_, 1);
                crate::leanh::lean_inc_ref(v_opts_1690_);
                crate::leanh::lean_dec(v___x_1689_);
                v___x_1691_ = l_Lean_Elab_pp_macroStack;
                v___x_1692_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_1690_, v___x_1691_);
                crate::leanh::lean_dec_ref(v_opts_1690_);
                if v___x_1692_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1683_);
                    v___x_1693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1693_, 0, v_msgData_1682_);
                    return v___x_1693_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1683_) == 0 {
                        v___x_1694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1694_, 0, v_msgData_1682_);
                        return v___x_1694_;
                    } else {
                        v_head_1695_ = crate::leanh::lean_ctor_get(v_macroStack_1683_, 0);
                        crate::leanh::lean_inc(v_head_1695_);
                        v_after_1696_ = crate::leanh::lean_ctor_get(v_head_1695_, 1);
                        v_isSharedCheck_1711_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1695_)) as u8;
                        if v_isSharedCheck_1711_ == 0 {
                            v_unused_1712_ = crate::leanh::lean_ctor_get(v_head_1695_, 0);
                            crate::leanh::lean_dec(v_unused_1712_);
                            v___x_1698_ = v_head_1695_;
                            v_isShared_1699_ = v_isSharedCheck_1711_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1696_);
                            crate::leanh::lean_dec(v_head_1695_);
                            v___x_1698_ = crate::leanh::lean_box(0);
                            v_isShared_1699_ = v_isSharedCheck_1711_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
                if v_isShared_1699_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1698_, 7);
                    crate::leanh::lean_ctor_set(v___x_1698_, 1, v___x_1700_);
                    crate::leanh::lean_ctor_set(v___x_1698_, 0, v_msgData_1682_);
                    v___x_1702_ = v___x_1698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_msgData_1682_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1700_);
                    v___x_1702_ = v_reuseFailAlloc_1710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1703_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2);
                v___x_1704_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v___x_1702_);
                crate::leanh::lean_ctor_set(v___x_1704_, 1, v___x_1703_);
                v___x_1705_ = l_Lean_MessageData_ofSyntax(v_after_1696_);
                v___x_1706_ = l_Lean_indentD(v___x_1705_);
                v_msgData_1707_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1707_, 0, v___x_1704_);
                crate::leanh::lean_ctor_set(v_msgData_1707_, 1, v___x_1706_);
                v___x_1708_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(v_msgData_1707_, v_macroStack_1683_);
                v___x_1709_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1709_, 0, v___x_1708_);
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_msgData_1713_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_1713_, v_macroStack_1714_, v___y_1715_);
    crate::leanh::lean_dec(v___y_1715_);
    return v_res_1717_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(
    mut v_msg_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1722_ = l_Lean_Elab_Command_getRef___redArg(v___y_1719_);
                if crate::leanh::lean_obj_tag(v___x_1722_) == 0 {
                    v_a_1723_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                    crate::leanh::lean_inc(v_a_1723_);
                    crate::leanh::lean_dec_ref_known(v___x_1722_, 1);
                    v_macroStack_1724_ = crate::leanh::lean_ctor_get(v___y_1719_, 4);
                    v___x_1725_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_1718_, v___y_1720_);
                    v_a_1726_ = crate::leanh::lean_ctor_get(v___x_1725_, 0);
                    crate::leanh::lean_inc(v_a_1726_);
                    crate::leanh::lean_dec_ref(v___x_1725_);
                    v___x_1727_ = l_Lean_Elab_getBetterRef(v_a_1723_, v_macroStack_1724_);
                    crate::leanh::lean_dec(v_a_1723_);
                    crate::leanh::lean_inc(v_macroStack_1724_);
                    v___x_1728_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_1726_, v_macroStack_1724_, v___y_1720_);
                    v_a_1729_ = crate::leanh::lean_ctor_get(v___x_1728_, 0);
                    v_isSharedCheck_1737_ = (!crate::leanh::lean_is_exclusive(v___x_1728_)) as u8;
                    if v_isSharedCheck_1737_ == 0 {
                        v___x_1731_ = v___x_1728_;
                        v_isShared_1732_ = v_isSharedCheck_1737_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1729_);
                        crate::leanh::lean_dec(v___x_1728_);
                        v___x_1731_ = crate::leanh::lean_box(0);
                        v_isShared_1732_ = v_isSharedCheck_1737_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1718_);
                    v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                    v_isSharedCheck_1745_ = (!crate::leanh::lean_is_exclusive(v___x_1722_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1740_ = v___x_1722_;
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1738_);
                        crate::leanh::lean_dec(v___x_1722_);
                        v___x_1740_ = crate::leanh::lean_box(0);
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1733_, 0, v___x_1727_);
                crate::leanh::lean_ctor_set(v___x_1733_, 1, v_a_1729_);
                if v_isShared_1732_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1731_, 1);
                    crate::leanh::lean_ctor_set(v___x_1731_, 0, v___x_1733_);
                    v___x_1735_ = v___x_1731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
                    v___x_1735_ = v_reuseFailAlloc_1736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1735_;
            }
            3 => {
                if v_isShared_1741_ == 0 {
                    v___x_1743_ = v___x_1740_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
                    v___x_1743_ = v_reuseFailAlloc_1744_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1743_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg___boxed(
    mut v_msg_1746_: *mut crate::leanh::LeanObject,
    mut v___y_1747_: *mut crate::leanh::LeanObject,
    mut v___y_1748_: *mut crate::leanh::LeanObject,
    mut v___y_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_1746_, v___y_1747_, v___y_1748_);
    crate::leanh::lean_dec(v___y_1748_);
    crate::leanh::lean_dec_ref(v___y_1747_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(
    mut v_ref_1751_: *mut crate::leanh::LeanObject,
    mut v_msg_1752_: *mut crate::leanh::LeanObject,
    mut v___y_1753_: *mut crate::leanh::LeanObject,
    mut v___y_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1767_: u8 = 0;
    let mut v_ref_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1756_ = l_Lean_Elab_Command_getRef___redArg(v___y_1753_);
                if crate::leanh::lean_obj_tag(v___x_1756_) == 0 {
                    v_a_1757_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                    crate::leanh::lean_inc(v_a_1757_);
                    crate::leanh::lean_dec_ref_known(v___x_1756_, 1);
                    v_fileName_1758_ = crate::leanh::lean_ctor_get(v___y_1753_, 0);
                    v_fileMap_1759_ = crate::leanh::lean_ctor_get(v___y_1753_, 1);
                    v_currRecDepth_1760_ = crate::leanh::lean_ctor_get(v___y_1753_, 2);
                    v_cmdPos_1761_ = crate::leanh::lean_ctor_get(v___y_1753_, 3);
                    v_macroStack_1762_ = crate::leanh::lean_ctor_get(v___y_1753_, 4);
                    v_quotContext_x3f_1763_ = crate::leanh::lean_ctor_get(v___y_1753_, 5);
                    v_currMacroScope_1764_ = crate::leanh::lean_ctor_get(v___y_1753_, 6);
                    v_snap_x3f_1765_ = crate::leanh::lean_ctor_get(v___y_1753_, 8);
                    v_cancelTk_x3f_1766_ = crate::leanh::lean_ctor_get(v___y_1753_, 9);
                    v_suppressElabErrors_1767_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_1753_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_1768_ = l_Lean_replaceRef(v_ref_1751_, v_a_1757_);
                    crate::leanh::lean_dec(v_a_1757_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_1766_);
                    crate::leanh::lean_inc(v_snap_x3f_1765_);
                    crate::leanh::lean_inc(v_currMacroScope_1764_);
                    crate::leanh::lean_inc(v_quotContext_x3f_1763_);
                    crate::leanh::lean_inc(v_macroStack_1762_);
                    crate::leanh::lean_inc(v_cmdPos_1761_);
                    crate::leanh::lean_inc(v_currRecDepth_1760_);
                    crate::leanh::lean_inc_ref(v_fileMap_1759_);
                    crate::leanh::lean_inc_ref(v_fileName_1758_);
                    v___x_1769_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_1769_, 0, v_fileName_1758_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 1, v_fileMap_1759_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 2, v_currRecDepth_1760_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 3, v_cmdPos_1761_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 4, v_macroStack_1762_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 5, v_quotContext_x3f_1763_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 6, v_currMacroScope_1764_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 7, v_ref_1768_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 8, v_snap_x3f_1765_);
                    crate::leanh::lean_ctor_set(v___x_1769_, 9, v_cancelTk_x3f_1766_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1769_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_1767_,
                    );
                    v___x_1770_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_1752_, v___x_1769_, v___y_1754_);
                    crate::leanh::lean_dec_ref_known(v___x_1769_, 10);
                    return v___x_1770_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1752_);
                    v_a_1771_ = crate::leanh::lean_ctor_get(v___x_1756_, 0);
                    v_isSharedCheck_1778_ = (!crate::leanh::lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1773_ = v___x_1756_;
                        v_isShared_1774_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1771_);
                        crate::leanh::lean_dec(v___x_1756_);
                        v___x_1773_ = crate::leanh::lean_box(0);
                        v_isShared_1774_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1774_ == 0 {
                    v___x_1776_ = v___x_1773_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
                    v___x_1776_ = v_reuseFailAlloc_1777_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1776_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg___boxed(
    mut v_ref_1779_: *mut crate::leanh::LeanObject,
    mut v_msg_1780_: *mut crate::leanh::LeanObject,
    mut v___y_1781_: *mut crate::leanh::LeanObject,
    mut v___y_1782_: *mut crate::leanh::LeanObject,
    mut v___y_1783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(
        v_ref_1779_,
        v_msg_1780_,
        v___y_1781_,
        v___y_1782_,
    );
    crate::leanh::lean_dec(v___y_1782_);
    crate::leanh::lean_dec_ref(v___y_1781_);
    crate::leanh::lean_dec(v_ref_1779_);
    return v_res_1784_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(
    mut v_k_1788_: *mut crate::leanh::LeanObject,
    mut v_as_1789_: *mut crate::leanh::LeanObject,
    mut v_sz_1790_: usize,
    mut v_i_1791_: usize,
    mut v_b_1792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: usize = 0;
    let mut v___x_1800_: usize = 0;
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1793_ = lean_usize_dec_lt(v_i_1791_, v_sz_1790_);
                if v___x_1793_ == 0 {
                    crate::leanh::lean_dec(v_k_1788_);
                    crate::leanh::lean_inc_ref(v_b_1792_);
                    return v_b_1792_;
                } else {
                    v___x_1794_ = crate::leanh::lean_box(0);
                    v_a_1795_ = lean_array_uget_borrowed(v_as_1789_, v_i_1791_);
                    crate::leanh::lean_inc(v_a_1795_);
                    v___x_1796_ = l_Lean_Syntax_getKind(v_a_1795_);
                    crate::leanh::lean_inc(v_k_1788_);
                    v___x_1797_ = l_Lean_Elab_Command_checkRuleKind(v___x_1796_, v_k_1788_);
                    crate::leanh::lean_dec(v___x_1796_);
                    if v___x_1797_ == 0 {
                        v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0;
                        v___x_1799_ = 1usize;
                        v___x_1800_ = lean_usize_add(v_i_1791_, v___x_1799_);
                        v_i_1791_ = v___x_1800_;
                        v_b_1792_ = v___x_1798_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_1788_);
                        crate::leanh::lean_inc(v_a_1795_);
                        v___x_1802_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1802_, 0, v_a_1795_);
                        v___x_1803_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1803_, 0, v___x_1802_);
                        v___x_1804_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1803_);
                        crate::leanh::lean_ctor_set(v___x_1804_, 1, v___x_1794_);
                        return v___x_1804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(
    mut v_k_1805_: *mut crate::leanh::LeanObject,
    mut v_as_1806_: *mut crate::leanh::LeanObject,
    mut v_sz_1807_: *mut crate::leanh::LeanObject,
    mut v_i_1808_: *mut crate::leanh::LeanObject,
    mut v_b_1809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1810_: usize = 0;
    let mut v_i_boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1810_ = crate::leanh::lean_unbox_usize(v_sz_1807_);
    crate::leanh::lean_dec(v_sz_1807_);
    v_i_boxed_1811_ = crate::leanh::lean_unbox_usize(v_i_1808_);
    crate::leanh::lean_dec(v_i_1808_);
    v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_1805_, v_as_1806_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1809_);
    crate::leanh::lean_dec_ref(v_b_1809_);
    crate::leanh::lean_dec_ref(v_as_1806_);
    return v_res_1812_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0;
    v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2;
    v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1832_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_1832_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16;
    v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
    return v___x_1839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(
    mut v_k_1840_: *mut crate::leanh::LeanObject,
    mut v_sz_1841_: usize,
    mut v_i_1842_: usize,
    mut v_bs_1843_: *mut crate::leanh::LeanObject,
    mut v___y_1844_: *mut crate::leanh::LeanObject,
    mut v___y_1845_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v___y_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pat_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quoted_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1920_: usize = 0;
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pat_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pats_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut v_a_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1945_: u8 = 0;
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut v_a_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v___x_1958_: u8 = 0;
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1847_ = lean_usize_dec_lt(v_i_1842_, v_sz_1841_);
                if v___x_1847_ == 0 {
                    crate::leanh::lean_dec(v_k_1840_);
                    v___x_1848_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1848_, 0, v_bs_1843_);
                    return v___x_1848_;
                } else {
                    v_v_1849_ = lean_array_uget(v_bs_1843_, v_i_1842_);
                    v___x_1850_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1851_ = lean_array_uset(v_bs_1843_, v_i_1842_, v___x_1850_);
                    v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8;
                    crate::leanh::lean_inc(v_v_1849_);
                    v___x_1879_ = l_Lean_Syntax_isOfKind(v_v_1849_, v___x_1878_);
                    if v___x_1879_ == 0 {
                        crate::leanh::lean_dec(v_v_1849_);
                        v___x_1880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                        v___y_1859_ = v___x_1880_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1881_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1882_ = l_Lean_Syntax_getArg(v_v_1849_, v___x_1881_);
                        crate::leanh::lean_inc(v___x_1882_);
                        v___x_1883_ = l_Lean_Syntax_matchesNull(v___x_1882_, v___x_1881_);
                        if v___x_1883_ == 0 {
                            crate::leanh::lean_dec(v___x_1882_);
                            crate::leanh::lean_dec(v_v_1849_);
                            v___x_1884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            v___y_1859_ = v___x_1884_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1885_ = l_Lean_Syntax_getArg(v___x_1882_, v___x_1850_);
                            crate::leanh::lean_dec(v___x_1882_);
                            v___x_1886_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1887_ = l_Lean_Syntax_getArg(v_v_1849_, v___x_1886_);
                            v___x_1901_ = l_Lean_Syntax_getArgs(v___x_1885_);
                            crate::leanh::lean_dec(v___x_1885_);
                            v___x_1902_ = crate::leanh::lean_box(0);
                            v_pat_1903_ = lean_array_get(v___x_1902_, v___x_1901_, v___x_1850_);
                            v___x_1958_ = l_Lean_Syntax_isQuot(v_pat_1903_);
                            if v___x_1958_ == 0 {
                                if v___x_1883_ == 0 {
                                    v___y_1905_ = v___y_1844_;
                                    v___y_1906_ = v___y_1845_;
                                    state = 7;
                                    continue;
                                } else {
                                    v___x_1959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                                    if crate::leanh::lean_obj_tag(v___x_1959_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1959_, 1);
                                        v___y_1905_ = v___y_1844_;
                                        v___y_1906_ = v___y_1845_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_pat_1903_);
                                        crate::leanh::lean_dec_ref(v___x_1901_);
                                        crate::leanh::lean_dec(v___x_1887_);
                                        crate::leanh::lean_dec_ref(v_bs_x27_1851_);
                                        crate::leanh::lean_dec(v_v_1849_);
                                        crate::leanh::lean_dec(v_k_1840_);
                                        v_a_1960_ = crate::leanh::lean_ctor_get(v___x_1959_, 0);
                                        v_isSharedCheck_1967_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1959_)) as u8;
                                        if v_isSharedCheck_1967_ == 0 {
                                            v___x_1962_ = v___x_1959_;
                                            v_isShared_1963_ = v_isSharedCheck_1967_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1960_);
                                            crate::leanh::lean_dec(v___x_1959_);
                                            v___x_1962_ = crate::leanh::lean_box(0);
                                            v_isShared_1963_ = v_isSharedCheck_1967_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___y_1905_ = v___y_1844_;
                                v___y_1906_ = v___y_1845_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1854_ = 1usize;
                v___x_1855_ = lean_usize_add(v_i_1842_, v___x_1854_);
                v___x_1856_ = lean_array_uset(v_bs_x27_1851_, v_i_1842_, v_a_1853_);
                v_i_1842_ = v___x_1855_;
                v_bs_1843_ = v___x_1856_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_1859_) == 0 {
                    v_a_1860_ = crate::leanh::lean_ctor_get(v___y_1859_, 0);
                    crate::leanh::lean_inc(v_a_1860_);
                    crate::leanh::lean_dec_ref_known(v___y_1859_, 1);
                    v_a_1853_ = v_a_1860_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_1851_);
                    crate::leanh::lean_dec(v_k_1840_);
                    v_a_1861_ = crate::leanh::lean_ctor_get(v___y_1859_, 0);
                    v_isSharedCheck_1868_ = (!crate::leanh::lean_is_exclusive(v___y_1859_)) as u8;
                    if v_isSharedCheck_1868_ == 0 {
                        v___x_1863_ = v___y_1859_;
                        v_isShared_1864_ = v_isSharedCheck_1868_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1861_);
                        crate::leanh::lean_dec(v___y_1859_);
                        v___x_1863_ = crate::leanh::lean_box(0);
                        v_isShared_1864_ = v_isSharedCheck_1868_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1864_ == 0 {
                    v___x_1866_ = v___x_1863_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1867_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
                    v___x_1866_ = v_reuseFailAlloc_1867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1866_;
            }
            5 => {
                v___x_1872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
                crate::leanh::lean_inc(v_k_1840_);
                v___x_1873_ = l_Lean_MessageData_ofName(v_k_1840_);
                v___x_1874_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1874_, 0, v___x_1872_);
                crate::leanh::lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
                v___x_1876_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1876_, 0, v___x_1874_);
                crate::leanh::lean_ctor_set(v___x_1876_, 1, v___x_1875_);
                v___x_1877_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_1849_, v___x_1876_, v___y_1870_, v___y_1871_);
                crate::leanh::lean_dec(v_v_1849_);
                v___y_1859_ = v___x_1877_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9;
                crate::leanh::lean_inc_n(v___y_1890_, 4);
                v___x_1892_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1892_, 0, v___y_1890_);
                crate::leanh::lean_ctor_set(v___x_1892_, 1, v___x_1891_);
                v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                v___x_1894_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                v___x_1895_ = l_Array_append___redArg(v___x_1894_, v___y_1889_);
                crate::leanh::lean_dec_ref(v___y_1889_);
                v___x_1896_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1896_, 0, v___y_1890_);
                crate::leanh::lean_ctor_set(v___x_1896_, 1, v___x_1893_);
                crate::leanh::lean_ctor_set(v___x_1896_, 2, v___x_1895_);
                v___x_1897_ = l_Lean_Syntax_node1(v___y_1890_, v___x_1893_, v___x_1896_);
                v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13;
                v___x_1899_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1899_, 0, v___y_1890_);
                crate::leanh::lean_ctor_set(v___x_1899_, 1, v___x_1898_);
                v___x_1900_ = l_Lean_Syntax_node4(
                    v___y_1890_,
                    v___x_1878_,
                    v___x_1892_,
                    v___x_1897_,
                    v___x_1899_,
                    v___x_1887_,
                );
                v_a_1853_ = v___x_1900_;
                state = 1;
                continue;
            }
            7 => {
                crate::leanh::lean_inc(v_pat_1903_);
                v_quoted_1907_ = l_Lean_Syntax_getQuotContent(v_pat_1903_);
                crate::leanh::lean_inc(v_quoted_1907_);
                v_k_x27_1908_ = l_Lean_Syntax_getKind(v_quoted_1907_);
                crate::leanh::lean_inc(v_k_1840_);
                v___x_1909_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_1908_, v_k_1840_);
                if v___x_1909_ == 0 {
                    v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15;
                    v___x_1911_ = lean_name_eq(v_k_x27_1908_, v___x_1910_);
                    if v___x_1911_ == 0 {
                        crate::leanh::lean_dec(v_quoted_1907_);
                        crate::leanh::lean_dec(v_pat_1903_);
                        crate::leanh::lean_dec_ref(v___x_1901_);
                        crate::leanh::lean_dec(v___x_1887_);
                        v___x_1912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
                        v___x_1913_ = l_Lean_MessageData_ofName(v_k_x27_1908_);
                        v___x_1914_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1914_, 0, v___x_1912_);
                        crate::leanh::lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                        v___x_1915_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
                        v___x_1916_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1916_, 0, v___x_1914_);
                        crate::leanh::lean_ctor_set(v___x_1916_, 1, v___x_1915_);
                        v___x_1917_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_1849_, v___x_1916_, v___y_1905_, v___y_1906_);
                        crate::leanh::lean_dec(v_v_1849_);
                        v___y_1859_ = v___x_1917_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_x27_1908_);
                        v___x_1918_ = l_Lean_Syntax_getArgs(v_quoted_1907_);
                        crate::leanh::lean_dec(v_quoted_1907_);
                        v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0;
                        v_sz_1920_ = lean_array_size(v___x_1918_);
                        v___x_1921_ = 0usize;
                        crate::leanh::lean_inc(v_k_1840_);
                        v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_1840_, v___x_1918_, v_sz_1920_, v___x_1921_, v___x_1919_);
                        crate::leanh::lean_dec_ref(v___x_1918_);
                        v_fst_1923_ = crate::leanh::lean_ctor_get(v___x_1922_, 0);
                        crate::leanh::lean_inc(v_fst_1923_);
                        crate::leanh::lean_dec_ref(v___x_1922_);
                        if crate::leanh::lean_obj_tag(v_fst_1923_) == 0 {
                            crate::leanh::lean_dec(v_pat_1903_);
                            crate::leanh::lean_dec_ref(v___x_1901_);
                            crate::leanh::lean_dec(v___x_1887_);
                            v___y_1870_ = v___y_1905_;
                            v___y_1871_ = v___y_1906_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1924_ = crate::leanh::lean_ctor_get(v_fst_1923_, 0);
                            crate::leanh::lean_inc(v_val_1924_);
                            crate::leanh::lean_dec_ref_known(v_fst_1923_, 1);
                            if crate::leanh::lean_obj_tag(v_val_1924_) == 0 {
                                crate::leanh::lean_dec(v_pat_1903_);
                                crate::leanh::lean_dec_ref(v___x_1901_);
                                crate::leanh::lean_dec(v___x_1887_);
                                v___y_1870_ = v___y_1905_;
                                v___y_1871_ = v___y_1906_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_v_1849_);
                                v_val_1925_ = crate::leanh::lean_ctor_get(v_val_1924_, 0);
                                crate::leanh::lean_inc(v_val_1925_);
                                crate::leanh::lean_dec_ref_known(v_val_1924_, 1);
                                v___x_1926_ = l_Lean_Elab_Command_getRef___redArg(v___y_1905_);
                                if crate::leanh::lean_obj_tag(v___x_1926_) == 0 {
                                    v_a_1927_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                                    crate::leanh::lean_inc(v_a_1927_);
                                    crate::leanh::lean_dec_ref_known(v___x_1926_, 1);
                                    v___x_1928_ =
                                        l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1905_);
                                    if crate::leanh::lean_obj_tag(v___x_1928_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1928_, 1);
                                        v_quotContext_x3f_1929_ =
                                            crate::leanh::lean_ctor_get(v___y_1905_, 5);
                                        v_pat_1930_ = l_Lean_Syntax_setArg(
                                            v_pat_1903_,
                                            v___x_1881_,
                                            v_val_1925_,
                                        );
                                        v_pats_1931_ =
                                            lean_array_set(v___x_1901_, v___x_1850_, v_pat_1930_);
                                        v___x_1932_ =
                                            l_Lean_SourceInfo_fromRef(v_a_1927_, v___x_1909_);
                                        crate::leanh::lean_dec(v_a_1927_);
                                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_1929_) == 0
                                        {
                                            v___x_1933_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1906_);
                                            if crate::leanh::lean_obj_tag(v___x_1933_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_1933_, 1);
                                                v___y_1889_ = v_pats_1931_;
                                                v___y_1890_ = v___x_1932_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_1932_);
                                                crate::leanh::lean_dec_ref(v_pats_1931_);
                                                crate::leanh::lean_dec(v___x_1887_);
                                                crate::leanh::lean_dec_ref(v_bs_x27_1851_);
                                                crate::leanh::lean_dec(v_k_1840_);
                                                v_a_1934_ =
                                                    crate::leanh::lean_ctor_get(v___x_1933_, 0);
                                                v_isSharedCheck_1941_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_1933_))
                                                        as u8;
                                                if v_isSharedCheck_1941_ == 0 {
                                                    v___x_1936_ = v___x_1933_;
                                                    v_isShared_1937_ = v_isSharedCheck_1941_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_1934_);
                                                    crate::leanh::lean_dec(v___x_1933_);
                                                    v___x_1936_ = crate::leanh::lean_box(0);
                                                    v_isShared_1937_ = v_isSharedCheck_1941_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___y_1889_ = v_pats_1931_;
                                            v___y_1890_ = v___x_1932_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1927_);
                                        crate::leanh::lean_dec(v_val_1925_);
                                        crate::leanh::lean_dec(v_pat_1903_);
                                        crate::leanh::lean_dec_ref(v___x_1901_);
                                        crate::leanh::lean_dec(v___x_1887_);
                                        crate::leanh::lean_dec_ref(v_bs_x27_1851_);
                                        crate::leanh::lean_dec(v_k_1840_);
                                        v_a_1942_ = crate::leanh::lean_ctor_get(v___x_1928_, 0);
                                        v_isSharedCheck_1949_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1928_)) as u8;
                                        if v_isSharedCheck_1949_ == 0 {
                                            v___x_1944_ = v___x_1928_;
                                            v_isShared_1945_ = v_isSharedCheck_1949_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1942_);
                                            crate::leanh::lean_dec(v___x_1928_);
                                            v___x_1944_ = crate::leanh::lean_box(0);
                                            v_isShared_1945_ = v_isSharedCheck_1949_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_1925_);
                                    crate::leanh::lean_dec(v_pat_1903_);
                                    crate::leanh::lean_dec_ref(v___x_1901_);
                                    crate::leanh::lean_dec(v___x_1887_);
                                    crate::leanh::lean_dec_ref(v_bs_x27_1851_);
                                    crate::leanh::lean_dec(v_k_1840_);
                                    v_a_1950_ = crate::leanh::lean_ctor_get(v___x_1926_, 0);
                                    v_isSharedCheck_1957_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1926_)) as u8;
                                    if v_isSharedCheck_1957_ == 0 {
                                        v___x_1952_ = v___x_1926_;
                                        v_isShared_1953_ = v_isSharedCheck_1957_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1950_);
                                        crate::leanh::lean_dec(v___x_1926_);
                                        v___x_1952_ = crate::leanh::lean_box(0);
                                        v_isShared_1953_ = v_isSharedCheck_1957_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_x27_1908_);
                    crate::leanh::lean_dec(v_quoted_1907_);
                    crate::leanh::lean_dec(v_pat_1903_);
                    crate::leanh::lean_dec_ref(v___x_1901_);
                    crate::leanh::lean_dec(v___x_1887_);
                    v_a_1853_ = v_v_1849_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v_isShared_1937_ == 0 {
                    v___x_1939_ = v___x_1936_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
                    v___x_1939_ = v_reuseFailAlloc_1940_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1939_;
            }
            10 => {
                if v_isShared_1945_ == 0 {
                    v___x_1947_ = v___x_1944_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
                    v___x_1947_ = v_reuseFailAlloc_1948_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1947_;
            }
            12 => {
                if v_isShared_1953_ == 0 {
                    v___x_1955_ = v___x_1952_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
                    v___x_1955_ = v_reuseFailAlloc_1956_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1955_;
            }
            14 => {
                if v_isShared_1963_ == 0 {
                    v___x_1965_ = v___x_1962_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
                    v___x_1965_ = v_reuseFailAlloc_1966_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___boxed(
    mut v_k_1968_: *mut crate::leanh::LeanObject,
    mut v_sz_1969_: *mut crate::leanh::LeanObject,
    mut v_i_1970_: *mut crate::leanh::LeanObject,
    mut v_bs_1971_: *mut crate::leanh::LeanObject,
    mut v___y_1972_: *mut crate::leanh::LeanObject,
    mut v___y_1973_: *mut crate::leanh::LeanObject,
    mut v___y_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1975_: usize = 0;
    let mut v_i_boxed_1976_: usize = 0;
    let mut v_res_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1975_ = crate::leanh::lean_unbox_usize(v_sz_1969_);
    crate::leanh::lean_dec(v_sz_1969_);
    v_i_boxed_1976_ = crate::leanh::lean_unbox_usize(v_i_1970_);
    crate::leanh::lean_dec(v_i_1970_);
    v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_1968_, v_sz_boxed_1975_, v_i_boxed_1976_, v_bs_1971_, v___y_1972_, v___y_1973_);
    crate::leanh::lean_dec(v___y_1973_);
    crate::leanh::lean_dec_ref(v___y_1972_);
    return v_res_1977_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1982_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__3;
    v___x_1983_ = l_String_toRawSubstring_x27(v___x_1982_);
    return v___x_1983_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
    v___x_1989_ = l_String_toRawSubstring_x27(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
    v___x_2002_ = l_String_toRawSubstring_x27(v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2016_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__25;
    v___x_2017_ = l_String_toRawSubstring_x27(v___x_2016_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRulesAux(
    mut v_doc_x3f_2044_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_2045_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2046_: *mut crate::leanh::LeanObject,
    mut v_tk_2047_: *mut crate::leanh::LeanObject,
    mut v_k_2048_: *mut crate::leanh::LeanObject,
    mut v_alts_2049_: *mut crate::leanh::LeanObject,
    mut v_a_2050_: *mut crate::leanh::LeanObject,
    mut v_a_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_2053_: usize = 0;
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___y_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___y_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_a_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2053_ = lean_array_size(v_alts_2049_);
                v___x_2054_ = 0usize;
                crate::leanh::lean_inc(v_k_2048_);
                v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_2048_, v_sz_2053_, v___x_2054_, v_alts_2049_, v_a_2050_, v_a_2051_);
                if crate::leanh::lean_obj_tag(v___x_2055_) == 0 {
                    v_a_2056_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2238_ = (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v___x_2058_ = v___x_2055_;
                        v_isShared_2059_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2056_);
                        crate::leanh::lean_dec(v___x_2055_);
                        v___x_2058_ = crate::leanh::lean_box(0);
                        v_isShared_2059_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_2048_);
                    crate::leanh::lean_dec(v_attrKind_2046_);
                    crate::leanh::lean_dec(v_doc_x3f_2044_);
                    v_a_2239_ = crate::leanh::lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2246_ = (!crate::leanh::lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2246_ == 0 {
                        v___x_2241_ = v___x_2055_;
                        v_isShared_2242_ = v_isSharedCheck_2246_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2239_);
                        crate::leanh::lean_dec(v___x_2055_);
                        v___x_2241_ = crate::leanh::lean_box(0);
                        v_isShared_2242_ = v_isSharedCheck_2246_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2186_ = l_Lean_Elab_Command_getRef___redArg(v_a_2050_);
                if crate::leanh::lean_obj_tag(v___x_2186_) == 0 {
                    v_a_2187_ = crate::leanh::lean_ctor_get(v___x_2186_, 0);
                    crate::leanh::lean_inc(v_a_2187_);
                    crate::leanh::lean_dec_ref_known(v___x_2186_, 1);
                    v___x_2188_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_2050_);
                    if crate::leanh::lean_obj_tag(v___x_2188_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2188_, 1);
                        v_quotContext_x3f_2189_ = crate::leanh::lean_ctor_get(v_a_2050_, 5);
                        v___x_2190_ = 0;
                        v___x_2210_ = l_Lean_SourceInfo_fromRef(v_a_2187_, v___x_2190_);
                        crate::leanh::lean_dec(v_a_2187_);
                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_2189_) == 0 {
                            v___x_2229_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_2051_);
                            crate::leanh::lean_dec_ref(v___x_2229_);
                            state = 8;
                            continue;
                        } else {
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2187_);
                        crate::leanh::lean_del_object(v___x_2058_);
                        crate::leanh::lean_dec(v_a_2056_);
                        crate::leanh::lean_dec(v_k_2048_);
                        crate::leanh::lean_dec(v_attrKind_2046_);
                        crate::leanh::lean_dec(v_doc_x3f_2044_);
                        v_a_2230_ = crate::leanh::lean_ctor_get(v___x_2188_, 0);
                        v_isSharedCheck_2237_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2188_)) as u8;
                        if v_isSharedCheck_2237_ == 0 {
                            v___x_2232_ = v___x_2188_;
                            v_isShared_2233_ = v_isSharedCheck_2237_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2230_);
                            crate::leanh::lean_dec(v___x_2188_);
                            v___x_2232_ = crate::leanh::lean_box(0);
                            v_isShared_2233_ = v_isSharedCheck_2237_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2058_);
                    crate::leanh::lean_dec(v_a_2056_);
                    crate::leanh::lean_dec(v_k_2048_);
                    crate::leanh::lean_dec(v_attrKind_2046_);
                    crate::leanh::lean_dec(v_doc_x3f_2044_);
                    return v___x_2186_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_2067_, 3);
                v___x_2072_ = l_Array_append___redArg(v___y_2067_, v___y_2071_);
                crate::leanh::lean_dec_ref(v___y_2071_);
                crate::leanh::lean_inc_n(v___y_2068_, 8);
                crate::leanh::lean_inc_n(v___y_2069_, 29);
                v___x_2073_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2073_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2073_, 1, v___y_2068_);
                crate::leanh::lean_ctor_set(v___x_2073_, 2, v___x_2072_);
                v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5;
                v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6;
                v___x_2076_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_2066_, 9);
                v___x_2077_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2076_);
                v___x_2078_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
                v___x_2079_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2079_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2079_, 1, v___x_2078_);
                v___x_2080_ = l_Array_append___redArg(v___y_2067_, v___y_2063_);
                crate::leanh::lean_dec_ref(v___y_2063_);
                v___x_2081_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2081_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2081_, 1, v___y_2068_);
                crate::leanh::lean_ctor_set(v___x_2081_, 2, v___x_2080_);
                v___x_2082_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
                v___x_2083_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2083_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2083_, 1, v___x_2082_);
                v___x_2084_ = l_Lean_Syntax_node3(
                    v___y_2069_,
                    v___x_2077_,
                    v___x_2079_,
                    v___x_2081_,
                    v___x_2083_,
                );
                v___x_2085_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2084_);
                crate::leanh::lean_inc_ref(v___y_2062_);
                v___x_2086_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2086_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2086_, 1, v___y_2062_);
                v___x_2087_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4,
                );
                v___x_2088_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
                crate::leanh::lean_inc_n(v___y_2065_, 3);
                crate::leanh::lean_inc_n(v___y_2061_, 3);
                v___x_2089_ = l_Lean_addMacroScope(v___y_2061_, v___x_2088_, v___y_2065_);
                v___x_2090_ = crate::leanh::lean_box(0);
                v___x_2091_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2091_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2091_, 1, v___x_2087_);
                crate::leanh::lean_ctor_set(v___x_2091_, 2, v___x_2089_);
                crate::leanh::lean_ctor_set(v___x_2091_, 3, v___x_2090_);
                v___x_2092_ = 1;
                v___x_2093_ = l_Lean_mkIdentFrom(v_tk_2047_, v_k_2048_, v___x_2092_);
                v___x_2094_ =
                    l_Lean_Syntax_node2(v___y_2069_, v___y_2068_, v___x_2091_, v___x_2093_);
                v___x_2095_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
                v___x_2096_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2096_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                v___x_2097_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
                v___x_2098_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8,
                );
                v___x_2099_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
                v___x_2100_ = l_Lean_addMacroScope(v___y_2061_, v___x_2099_, v___y_2065_);
                v___x_2101_ = l_Lean_Name_mkStr2(v___y_2066_, v___x_2097_);
                crate::leanh::lean_inc(v___x_2101_);
                v___x_2102_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2102_, 0, v___x_2101_);
                crate::leanh::lean_ctor_set(v___x_2102_, 1, v___x_2090_);
                v___x_2103_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2103_, 0, v___x_2101_);
                v___x_2104_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2104_, 0, v___x_2103_);
                crate::leanh::lean_ctor_set(v___x_2104_, 1, v___x_2090_);
                v___x_2105_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2105_, 0, v___x_2102_);
                crate::leanh::lean_ctor_set(v___x_2105_, 1, v___x_2104_);
                v___x_2106_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2106_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2106_, 1, v___x_2098_);
                crate::leanh::lean_ctor_set(v___x_2106_, 2, v___x_2100_);
                crate::leanh::lean_ctor_set(v___x_2106_, 3, v___x_2105_);
                v___x_2107_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
                v___x_2108_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2108_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2108_, 1, v___x_2107_);
                v___x_2109_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
                v___x_2110_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2109_);
                v___x_2111_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2111_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2111_, 1, v___x_2109_);
                v___x_2112_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
                v___x_2113_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2112_);
                v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7;
                v___x_2115_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2114_);
                v___x_2116_ = l_Array_append___redArg(v___y_2067_, v_a_2056_);
                crate::leanh::lean_dec(v_a_2056_);
                v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9;
                v___x_2118_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2118_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2118_, 1, v___x_2117_);
                v___x_2119_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
                v___x_2120_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2119_);
                v___x_2121_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__14;
                v___x_2122_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2122_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2122_, 1, v___x_2121_);
                v___x_2123_ = l_Lean_Syntax_node1(v___y_2069_, v___x_2120_, v___x_2122_);
                v___x_2124_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2123_);
                v___x_2125_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2124_);
                v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13;
                v___x_2127_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2127_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2127_, 1, v___x_2126_);
                v___x_2128_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__15;
                v___x_2129_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2128_);
                v___x_2130_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__16;
                v___x_2131_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2131_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2131_, 1, v___x_2130_);
                v___x_2132_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
                v___x_2133_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2132_);
                v___x_2134_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__19),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once
                    ),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19,
                );
                v___x_2135_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
                v___x_2136_ = l_Lean_addMacroScope(v___y_2061_, v___x_2135_, v___y_2065_);
                v___x_2137_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__24;
                v___x_2138_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2138_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2134_);
                crate::leanh::lean_ctor_set(v___x_2138_, 2, v___x_2136_);
                crate::leanh::lean_ctor_set(v___x_2138_, 3, v___x_2137_);
                v___x_2139_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__26),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once
                    ),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26,
                );
                v___x_2140_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__27;
                v___x_2141_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__28;
                v___x_2142_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2097_, v___x_2140_, v___x_2141_);
                crate::leanh::lean_inc_n(v___x_2142_, 2);
                v___x_2143_ = l_Lean_addMacroScope(v___y_2061_, v___x_2142_, v___y_2065_);
                v___x_2144_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2144_, 0, v___x_2142_);
                crate::leanh::lean_ctor_set(v___x_2144_, 1, v___x_2090_);
                v___x_2145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2145_, 0, v___x_2142_);
                v___x_2146_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                crate::leanh::lean_ctor_set(v___x_2146_, 1, v___x_2090_);
                v___x_2147_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2144_);
                crate::leanh::lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                v___x_2148_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2148_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2148_, 1, v___x_2139_);
                crate::leanh::lean_ctor_set(v___x_2148_, 2, v___x_2143_);
                crate::leanh::lean_ctor_set(v___x_2148_, 3, v___x_2147_);
                v___x_2149_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2148_);
                v___x_2150_ =
                    l_Lean_Syntax_node2(v___y_2069_, v___x_2133_, v___x_2138_, v___x_2149_);
                v___x_2151_ =
                    l_Lean_Syntax_node2(v___y_2069_, v___x_2129_, v___x_2131_, v___x_2150_);
                v___x_2152_ = l_Lean_Syntax_node4(
                    v___y_2069_,
                    v___x_2115_,
                    v___x_2118_,
                    v___x_2125_,
                    v___x_2127_,
                    v___x_2151_,
                );
                v___x_2153_ = lean_array_push(v___x_2116_, v___x_2152_);
                v___x_2154_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2154_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2154_, 1, v___y_2068_);
                crate::leanh::lean_ctor_set(v___x_2154_, 2, v___x_2153_);
                v___x_2155_ = l_Lean_Syntax_node1(v___y_2069_, v___x_2113_, v___x_2154_);
                v___x_2156_ =
                    l_Lean_Syntax_node2(v___y_2069_, v___x_2110_, v___x_2111_, v___x_2155_);
                v___x_2157_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2158_ = lean_mk_empty_array_with_capacity(v___x_2157_);
                v___x_2159_ = lean_array_push(v___x_2158_, v___x_2073_);
                v___x_2160_ = lean_array_push(v___x_2159_, v___x_2085_);
                v___x_2161_ = lean_array_push(v___x_2160_, v___y_2064_);
                v___x_2162_ = lean_array_push(v___x_2161_, v___x_2086_);
                v___x_2163_ = lean_array_push(v___x_2162_, v___x_2094_);
                v___x_2164_ = lean_array_push(v___x_2163_, v___x_2096_);
                v___x_2165_ = lean_array_push(v___x_2164_, v___x_2106_);
                v___x_2166_ = lean_array_push(v___x_2165_, v___x_2108_);
                v___x_2167_ = lean_array_push(v___x_2166_, v___x_2156_);
                crate::leanh::lean_inc(v___y_2070_);
                v___x_2168_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2168_, 0, v___y_2069_);
                crate::leanh::lean_ctor_set(v___x_2168_, 1, v___y_2070_);
                crate::leanh::lean_ctor_set(v___x_2168_, 2, v___x_2167_);
                if v_isShared_2059_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2058_, 0, v___x_2168_);
                    v___x_2170_ = v___x_2058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
                    v___x_2170_ = v_reuseFailAlloc_2171_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2170_;
            }
            4 => {
                v___x_2178_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4;
                v___x_2179_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__31;
                v___x_2180_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__32;
                v___x_2181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                v___x_2182_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                if crate::leanh::lean_obj_tag(v_doc_x3f_2044_) == 1 {
                    v_val_2183_ = crate::leanh::lean_ctor_get(v_doc_x3f_2044_, 0);
                    crate::leanh::lean_inc(v_val_2183_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_2044_, 1);
                    v___x_2184_ = l_Array_mkArray1___redArg(v_val_2183_);
                    v___y_2061_ = v_a_2177_;
                    v___y_2062_ = v___x_2179_;
                    v___y_2063_ = v___y_2173_;
                    v___y_2064_ = v___y_2174_;
                    v___y_2065_ = v___y_2175_;
                    v___y_2066_ = v___x_2178_;
                    v___y_2067_ = v___x_2182_;
                    v___y_2068_ = v___x_2181_;
                    v___y_2069_ = v___y_2176_;
                    v___y_2070_ = v___x_2180_;
                    v___y_2071_ = v___x_2184_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_2044_);
                    v___x_2185_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__33;
                    v___y_2061_ = v_a_2177_;
                    v___y_2062_ = v___x_2179_;
                    v___y_2063_ = v___y_2173_;
                    v___y_2064_ = v___y_2174_;
                    v___y_2065_ = v___y_2175_;
                    v___y_2066_ = v___x_2178_;
                    v___y_2067_ = v___x_2182_;
                    v___y_2068_ = v___x_2181_;
                    v___y_2069_ = v___y_2176_;
                    v___y_2070_ = v___x_2180_;
                    v___y_2071_ = v___x_2185_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_2193_ = l_Lean_Elab_Command_getRef___redArg(v_a_2050_);
                if crate::leanh::lean_obj_tag(v___x_2193_) == 0 {
                    v_a_2194_ = crate::leanh::lean_ctor_get(v___x_2193_, 0);
                    crate::leanh::lean_inc(v_a_2194_);
                    crate::leanh::lean_dec_ref_known(v___x_2193_, 1);
                    v___x_2195_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_2050_);
                    if crate::leanh::lean_obj_tag(v___x_2195_) == 0 {
                        v_a_2196_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                        crate::leanh::lean_inc(v_a_2196_);
                        crate::leanh::lean_dec_ref_known(v___x_2195_, 1);
                        v___x_2197_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_2046_);
                        v___x_2198_ = l_Lean_SourceInfo_fromRef(v_a_2194_, v___x_2190_);
                        crate::leanh::lean_dec(v_a_2194_);
                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_2189_) == 0 {
                            v___x_2199_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_2051_);
                            v_a_2200_ = crate::leanh::lean_ctor_get(v___x_2199_, 0);
                            crate::leanh::lean_inc(v_a_2200_);
                            crate::leanh::lean_dec_ref(v___x_2199_);
                            v___y_2173_ = v___y_2192_;
                            v___y_2174_ = v___x_2197_;
                            v___y_2175_ = v_a_2196_;
                            v___y_2176_ = v___x_2198_;
                            v_a_2177_ = v_a_2200_;
                            state = 4;
                            continue;
                        } else {
                            v_val_2201_ = crate::leanh::lean_ctor_get(v_quotContext_x3f_2189_, 0);
                            crate::leanh::lean_inc(v_val_2201_);
                            v___y_2173_ = v___y_2192_;
                            v___y_2174_ = v___x_2197_;
                            v___y_2175_ = v_a_2196_;
                            v___y_2176_ = v___x_2198_;
                            v_a_2177_ = v_val_2201_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2194_);
                        crate::leanh::lean_dec_ref(v___y_2192_);
                        crate::leanh::lean_del_object(v___x_2058_);
                        crate::leanh::lean_dec(v_a_2056_);
                        crate::leanh::lean_dec(v_k_2048_);
                        crate::leanh::lean_dec(v_attrKind_2046_);
                        crate::leanh::lean_dec(v_doc_x3f_2044_);
                        v_a_2202_ = crate::leanh::lean_ctor_get(v___x_2195_, 0);
                        v_isSharedCheck_2209_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2195_)) as u8;
                        if v_isSharedCheck_2209_ == 0 {
                            v___x_2204_ = v___x_2195_;
                            v_isShared_2205_ = v_isSharedCheck_2209_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2202_);
                            crate::leanh::lean_dec(v___x_2195_);
                            v___x_2204_ = crate::leanh::lean_box(0);
                            v_isShared_2205_ = v_isSharedCheck_2209_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2192_);
                    crate::leanh::lean_del_object(v___x_2058_);
                    crate::leanh::lean_dec(v_a_2056_);
                    crate::leanh::lean_dec(v_k_2048_);
                    crate::leanh::lean_dec(v_attrKind_2046_);
                    crate::leanh::lean_dec(v_doc_x3f_2044_);
                    return v___x_2193_;
                }
            }
            6 => {
                if v_isShared_2205_ == 0 {
                    v___x_2207_ = v___x_2204_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
                    v___x_2207_ = v_reuseFailAlloc_2208_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2207_;
            }
            8 => {
                v___x_2212_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__35;
                v___x_2213_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__37;
                v___x_2214_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__38;
                crate::leanh::lean_inc_n(v___x_2210_, 2);
                v___x_2215_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2210_);
                crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2213_);
                crate::leanh::lean_inc(v_k_2048_);
                v___x_2216_ = lean_mk_syntax_ident(v_k_2048_);
                v___x_2217_ =
                    l_Lean_Syntax_node2(v___x_2210_, v___x_2214_, v___x_2215_, v___x_2216_);
                crate::leanh::lean_inc(v_attrKind_2046_);
                v___x_2218_ =
                    l_Lean_Syntax_node2(v___x_2210_, v___x_2212_, v_attrKind_2046_, v___x_2217_);
                if crate::leanh::lean_obj_tag(v_attrs_x3f_2045_) == 0 {
                    v___x_2219_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2220_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
                    v___x_2222_ = lean_array_push(v___x_2221_, v___x_2218_);
                    v___x_2223_ = l_Lean_Syntax_SepArray_ofElems(v___x_2219_, v___x_2222_);
                    crate::leanh::lean_dec_ref(v___x_2222_);
                    v___y_2192_ = v___x_2223_;
                    state = 5;
                    continue;
                } else {
                    v_val_2224_ = crate::leanh::lean_ctor_get(v_attrs_x3f_2045_, 0);
                    v___x_2225_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2226_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_2224_);
                    v___x_2227_ = lean_array_push(v___x_2226_, v___x_2218_);
                    v___x_2228_ = l_Lean_Syntax_SepArray_ofElems(v___x_2225_, v___x_2227_);
                    crate::leanh::lean_dec_ref(v___x_2227_);
                    v___y_2192_ = v___x_2228_;
                    state = 5;
                    continue;
                }
            }
            9 => {
                if v_isShared_2233_ == 0 {
                    v___x_2235_ = v___x_2232_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
                    v___x_2235_ = v_reuseFailAlloc_2236_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2235_;
            }
            11 => {
                if v_isShared_2242_ == 0 {
                    v___x_2244_ = v___x_2241_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
                    v___x_2244_ = v_reuseFailAlloc_2245_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRulesAux___boxed(
    mut v_doc_x3f_2247_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_2248_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2249_: *mut crate::leanh::LeanObject,
    mut v_tk_2250_: *mut crate::leanh::LeanObject,
    mut v_k_2251_: *mut crate::leanh::LeanObject,
    mut v_alts_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
    mut v_a_2254_: *mut crate::leanh::LeanObject,
    mut v_a_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_Elab_Command_elabMacroRulesAux(
        v_doc_x3f_2247_,
        v_attrs_x3f_2248_,
        v_attrKind_2249_,
        v_tk_2250_,
        v_k_2251_,
        v_alts_2252_,
        v_a_2253_,
        v_a_2254_,
    );
    crate::leanh::lean_dec(v_a_2254_);
    crate::leanh::lean_dec_ref(v_a_2253_);
    crate::leanh::lean_dec(v_tk_2250_);
    crate::leanh::lean_dec(v_attrs_x3f_2248_);
    return v_res_2256_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(
    mut v_00_u03b1_2257_: *mut crate::leanh::LeanObject,
    mut v_ref_2258_: *mut crate::leanh::LeanObject,
    mut v_msg_2259_: *mut crate::leanh::LeanObject,
    mut v___y_2260_: *mut crate::leanh::LeanObject,
    mut v___y_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(
        v_ref_2258_,
        v_msg_2259_,
        v___y_2260_,
        v___y_2261_,
    );
    return v___x_2263_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(
    mut v_00_u03b1_2264_: *mut crate::leanh::LeanObject,
    mut v_ref_2265_: *mut crate::leanh::LeanObject,
    mut v_msg_2266_: *mut crate::leanh::LeanObject,
    mut v___y_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(
        v_00_u03b1_2264_,
        v_ref_2265_,
        v_msg_2266_,
        v___y_2267_,
        v___y_2268_,
    );
    crate::leanh::lean_dec(v___y_2268_);
    crate::leanh::lean_dec_ref(v___y_2267_);
    crate::leanh::lean_dec(v_ref_2265_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(
    mut v_msgData_2271_: *mut crate::leanh::LeanObject,
    mut v___y_2272_: *mut crate::leanh::LeanObject,
    mut v___y_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_2271_, v___y_2273_);
    return v___x_2275_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_2276_, v___y_2277_, v___y_2278_);
    crate::leanh::lean_dec(v___y_2278_);
    crate::leanh::lean_dec_ref(v___y_2277_);
    return v_res_2280_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(
    mut v_00_u03b1_2281_: *mut crate::leanh::LeanObject,
    mut v_msg_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_2282_, v___y_2283_, v___y_2284_);
    return v___x_2286_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(
    mut v_00_u03b1_2287_: *mut crate::leanh::LeanObject,
    mut v_msg_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2292_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_2287_, v_msg_2288_, v___y_2289_, v___y_2290_);
    crate::leanh::lean_dec(v___y_2290_);
    crate::leanh::lean_dec_ref(v___y_2289_);
    return v_res_2292_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(
    mut v_msgData_2293_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2294_: *mut crate::leanh::LeanObject,
    mut v___y_2295_: *mut crate::leanh::LeanObject,
    mut v___y_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_2293_, v_macroStack_2294_, v___y_2296_);
    return v___x_2298_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(
    mut v_msgData_2299_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2300_: *mut crate::leanh::LeanObject,
    mut v___y_2301_: *mut crate::leanh::LeanObject,
    mut v___y_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2304_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_2299_, v_macroStack_2300_, v___y_2301_, v___y_2302_);
    crate::leanh::lean_dec(v___y_2302_);
    crate::leanh::lean_dec_ref(v___y_2301_);
    return v_res_2304_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2306_: u8,
    mut v_a_x3f_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2309_ = lean_st_ref_take(v___y_2305_);
                v_env_2310_ = crate::leanh::lean_ctor_get(v___x_2309_, 0);
                v_messages_2311_ = crate::leanh::lean_ctor_get(v___x_2309_, 1);
                v_scopes_2312_ = crate::leanh::lean_ctor_get(v___x_2309_, 2);
                v_usedQuotCtxts_2313_ = crate::leanh::lean_ctor_get(v___x_2309_, 3);
                v_nextMacroScope_2314_ = crate::leanh::lean_ctor_get(v___x_2309_, 4);
                v_maxRecDepth_2315_ = crate::leanh::lean_ctor_get(v___x_2309_, 5);
                v_ngen_2316_ = crate::leanh::lean_ctor_get(v___x_2309_, 6);
                v_auxDeclNGen_2317_ = crate::leanh::lean_ctor_get(v___x_2309_, 7);
                v_infoState_2318_ = crate::leanh::lean_ctor_get(v___x_2309_, 8);
                v_traceState_2319_ = crate::leanh::lean_ctor_get(v___x_2309_, 9);
                v_snapshotTasks_2320_ = crate::leanh::lean_ctor_get(v___x_2309_, 10);
                v_isSharedCheck_2331_ = (!crate::leanh::lean_is_exclusive(v___x_2309_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v___x_2322_ = v___x_2309_;
                    v_isShared_2323_ = v_isSharedCheck_2331_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2320_);
                    crate::leanh::lean_inc(v_traceState_2319_);
                    crate::leanh::lean_inc(v_infoState_2318_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2317_);
                    crate::leanh::lean_inc(v_ngen_2316_);
                    crate::leanh::lean_inc(v_maxRecDepth_2315_);
                    crate::leanh::lean_inc(v_nextMacroScope_2314_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2313_);
                    crate::leanh::lean_inc(v_scopes_2312_);
                    crate::leanh::lean_inc(v_messages_2311_);
                    crate::leanh::lean_inc(v_env_2310_);
                    crate::leanh::lean_dec(v___x_2309_);
                    v___x_2322_ = crate::leanh::lean_box(0);
                    v_isShared_2323_ = v_isSharedCheck_2331_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2324_ = l_Lean_Environment_setExporting(v_env_2310_, v_isExporting_2306_);
                if v_isShared_2323_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2322_, 0, v___x_2324_);
                    v___x_2326_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2324_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_messages_2311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_scopes_2312_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_usedQuotCtxts_2313_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_nextMacroScope_2314_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 5, v_maxRecDepth_2315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 6, v_ngen_2316_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 7, v_auxDeclNGen_2317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 8, v_infoState_2318_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 9, v_traceState_2319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 10, v_snapshotTasks_2320_);
                    v___x_2326_ = v_reuseFailAlloc_2330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2327_ = lean_st_ref_set(v___y_2305_, v___x_2326_);
                v___x_2328_ = crate::leanh::lean_box(0);
                v___x_2329_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2329_, 0, v___x_2328_);
                return v___x_2329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2333_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2336_: u8 = 0;
    let mut v_res_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2336_ = (crate::leanh::lean_unbox(v_isExporting_2333_) as u8);
    v_res_2337_ =
        l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(
            v___y_2332_,
            v_isExporting_boxed_2336_,
            v_a_x3f_2334_,
        );
    crate::leanh::lean_dec(v_a_x3f_2334_);
    crate::leanh::lean_dec(v___y_2332_);
    return v_res_2337_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(
    mut v_x_2338_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2339_: u8,
    mut v___y_2340_: *mut crate::leanh::LeanObject,
    mut v___y_2341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2345_: u8 = 0;
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_unused_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_a_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut v_unused_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2343_ = lean_st_ref_get(v___y_2341_);
                v_env_2344_ = crate::leanh::lean_ctor_get(v___x_2343_, 0);
                crate::leanh::lean_inc_ref(v_env_2344_);
                crate::leanh::lean_dec(v___x_2343_);
                v_isExporting_2345_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2344_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_2344_);
                v___x_2346_ = lean_st_ref_take(v___y_2341_);
                v_env_2347_ = crate::leanh::lean_ctor_get(v___x_2346_, 0);
                v_messages_2348_ = crate::leanh::lean_ctor_get(v___x_2346_, 1);
                v_scopes_2349_ = crate::leanh::lean_ctor_get(v___x_2346_, 2);
                v_usedQuotCtxts_2350_ = crate::leanh::lean_ctor_get(v___x_2346_, 3);
                v_nextMacroScope_2351_ = crate::leanh::lean_ctor_get(v___x_2346_, 4);
                v_maxRecDepth_2352_ = crate::leanh::lean_ctor_get(v___x_2346_, 5);
                v_ngen_2353_ = crate::leanh::lean_ctor_get(v___x_2346_, 6);
                v_auxDeclNGen_2354_ = crate::leanh::lean_ctor_get(v___x_2346_, 7);
                v_infoState_2355_ = crate::leanh::lean_ctor_get(v___x_2346_, 8);
                v_traceState_2356_ = crate::leanh::lean_ctor_get(v___x_2346_, 9);
                v_snapshotTasks_2357_ = crate::leanh::lean_ctor_get(v___x_2346_, 10);
                v_isSharedCheck_2395_ = (!crate::leanh::lean_is_exclusive(v___x_2346_)) as u8;
                if v_isSharedCheck_2395_ == 0 {
                    v___x_2359_ = v___x_2346_;
                    v_isShared_2360_ = v_isSharedCheck_2395_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2357_);
                    crate::leanh::lean_inc(v_traceState_2356_);
                    crate::leanh::lean_inc(v_infoState_2355_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2354_);
                    crate::leanh::lean_inc(v_ngen_2353_);
                    crate::leanh::lean_inc(v_maxRecDepth_2352_);
                    crate::leanh::lean_inc(v_nextMacroScope_2351_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2350_);
                    crate::leanh::lean_inc(v_scopes_2349_);
                    crate::leanh::lean_inc(v_messages_2348_);
                    crate::leanh::lean_inc(v_env_2347_);
                    crate::leanh::lean_dec(v___x_2346_);
                    v___x_2359_ = crate::leanh::lean_box(0);
                    v_isShared_2360_ = v_isSharedCheck_2395_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2361_ = l_Lean_Environment_setExporting(v_env_2347_, v_isExporting_2339_);
                if v_isShared_2360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2359_, 0, v___x_2361_);
                    v___x_2363_ = v___x_2359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_messages_2348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_scopes_2349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_usedQuotCtxts_2350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_nextMacroScope_2351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 5, v_maxRecDepth_2352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 6, v_ngen_2353_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 7, v_auxDeclNGen_2354_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 8, v_infoState_2355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 9, v_traceState_2356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 10, v_snapshotTasks_2357_);
                    v___x_2363_ = v_reuseFailAlloc_2394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2364_ = lean_st_ref_set(v___y_2341_, v___x_2363_);
                crate::leanh::lean_inc(v___y_2341_);
                crate::leanh::lean_inc_ref(v___y_2340_);
                v_r_2365_ = crate::leanh::lean_apply_3(
                    v_x_2338_,
                    v___y_2340_,
                    v___y_2341_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_2365_) == 0 {
                    v_a_2366_ = crate::leanh::lean_ctor_get(v_r_2365_, 0);
                    v_isSharedCheck_2382_ = (!crate::leanh::lean_is_exclusive(v_r_2365_)) as u8;
                    if v_isSharedCheck_2382_ == 0 {
                        v___x_2368_ = v_r_2365_;
                        v_isShared_2369_ = v_isSharedCheck_2382_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2366_);
                        crate::leanh::lean_dec(v_r_2365_);
                        v___x_2368_ = crate::leanh::lean_box(0);
                        v_isShared_2369_ = v_isSharedCheck_2382_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2383_ = crate::leanh::lean_ctor_get(v_r_2365_, 0);
                    crate::leanh::lean_inc(v_a_2383_);
                    crate::leanh::lean_dec_ref_known(v_r_2365_, 1);
                    v___x_2384_ = crate::leanh::lean_box(0);
                    v___x_2385_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_2341_, v_isExporting_2345_, v___x_2384_);
                    v_isSharedCheck_2392_ = (!crate::leanh::lean_is_exclusive(v___x_2385_)) as u8;
                    if v_isSharedCheck_2392_ == 0 {
                        v_unused_2393_ = crate::leanh::lean_ctor_get(v___x_2385_, 0);
                        crate::leanh::lean_dec(v_unused_2393_);
                        v___x_2387_ = v___x_2385_;
                        v_isShared_2388_ = v_isSharedCheck_2392_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2385_);
                        v___x_2387_ = crate::leanh::lean_box(0);
                        v_isShared_2388_ = v_isSharedCheck_2392_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                crate::leanh::lean_inc(v_a_2366_);
                if v_isShared_2369_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2368_, 1);
                    v___x_2371_ = v___x_2368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2366_);
                    v___x_2371_ = v_reuseFailAlloc_2381_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2372_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_2341_, v_isExporting_2345_, v___x_2371_);
                crate::leanh::lean_dec_ref(v___x_2371_);
                v_isSharedCheck_2379_ = (!crate::leanh::lean_is_exclusive(v___x_2372_)) as u8;
                if v_isSharedCheck_2379_ == 0 {
                    v_unused_2380_ = crate::leanh::lean_ctor_get(v___x_2372_, 0);
                    crate::leanh::lean_dec(v_unused_2380_);
                    v___x_2374_ = v___x_2372_;
                    v_isShared_2375_ = v_isSharedCheck_2379_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2372_);
                    v___x_2374_ = crate::leanh::lean_box(0);
                    v_isShared_2375_ = v_isSharedCheck_2379_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2374_, 0, v_a_2366_);
                    v___x_2377_ = v___x_2374_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2366_);
                    v___x_2377_ = v_reuseFailAlloc_2378_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2377_;
            }
            7 => {
                if v_isShared_2388_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2387_, 1);
                    crate::leanh::lean_ctor_set(v___x_2387_, 0, v_a_2383_);
                    v___x_2390_ = v___x_2387_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2383_);
                    v___x_2390_ = v_reuseFailAlloc_2391_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___boxed(
    mut v_x_2396_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2397_: *mut crate::leanh::LeanObject,
    mut v___y_2398_: *mut crate::leanh::LeanObject,
    mut v___y_2399_: *mut crate::leanh::LeanObject,
    mut v___y_2400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2401_: u8 = 0;
    let mut v_res_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2401_ = (crate::leanh::lean_unbox(v_isExporting_2397_) as u8);
    v_res_2402_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(
        v_x_2396_,
        v_isExporting_boxed_2401_,
        v___y_2398_,
        v___y_2399_,
    );
    crate::leanh::lean_dec(v___y_2399_);
    crate::leanh::lean_dec_ref(v___y_2398_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(
    mut v_00_u03b1_2403_: *mut crate::leanh::LeanObject,
    mut v_x_2404_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2405_: u8,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(
        v_x_2404_,
        v_isExporting_2405_,
        v___y_2406_,
        v___y_2407_,
    );
    return v___x_2409_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(
    mut v_00_u03b1_2410_: *mut crate::leanh::LeanObject,
    mut v_x_2411_: *mut crate::leanh::LeanObject,
    mut v_isExporting_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
    mut v___y_2414_: *mut crate::leanh::LeanObject,
    mut v___y_2415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_2416_: u8 = 0;
    let mut v_res_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2416_ = (crate::leanh::lean_unbox(v_isExporting_2412_) as u8);
    v_res_2417_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(
        v_00_u03b1_2410_,
        v_x_2411_,
        v_isExporting_boxed_2416_,
        v___y_2413_,
        v___y_2414_,
    );
    crate::leanh::lean_dec(v___y_2414_);
    crate::leanh::lean_dec_ref(v___y_2413_);
    return v_res_2417_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__0(
    mut v___x_2418_: *mut crate::leanh::LeanObject,
    mut v___x_2419_: *mut crate::leanh::LeanObject,
    mut v_doc_x3f_2420_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_2421_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2422_: *mut crate::leanh::LeanObject,
    mut v_tk_2423_: *mut crate::leanh::LeanObject,
    mut v_alts_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2439_: u8 = 0;
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v_ref_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_reuseFailAlloc_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v_unused_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Lean_Elab_Command_getRef___redArg(v___y_2425_);
                if crate::leanh::lean_obj_tag(v___x_2428_) == 0 {
                    v_a_2429_ = crate::leanh::lean_ctor_get(v___x_2428_, 0);
                    crate::leanh::lean_inc(v_a_2429_);
                    crate::leanh::lean_dec_ref_known(v___x_2428_, 1);
                    v_fileName_2430_ = crate::leanh::lean_ctor_get(v___y_2425_, 0);
                    v_fileMap_2431_ = crate::leanh::lean_ctor_get(v___y_2425_, 1);
                    v_currRecDepth_2432_ = crate::leanh::lean_ctor_get(v___y_2425_, 2);
                    v_cmdPos_2433_ = crate::leanh::lean_ctor_get(v___y_2425_, 3);
                    v_macroStack_2434_ = crate::leanh::lean_ctor_get(v___y_2425_, 4);
                    v_quotContext_x3f_2435_ = crate::leanh::lean_ctor_get(v___y_2425_, 5);
                    v_currMacroScope_2436_ = crate::leanh::lean_ctor_get(v___y_2425_, 6);
                    v_snap_x3f_2437_ = crate::leanh::lean_ctor_get(v___y_2425_, 8);
                    v_cancelTk_x3f_2438_ = crate::leanh::lean_ctor_get(v___y_2425_, 9);
                    v_suppressElabErrors_2439_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2425_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_isSharedCheck_2458_ = (!crate::leanh::lean_is_exclusive(v___y_2425_)) as u8;
                    if v_isSharedCheck_2458_ == 0 {
                        v_unused_2459_ = crate::leanh::lean_ctor_get(v___y_2425_, 7);
                        crate::leanh::lean_dec(v_unused_2459_);
                        v___x_2441_ = v___y_2425_;
                        v_isShared_2442_ = v_isSharedCheck_2458_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_cancelTk_x3f_2438_);
                        crate::leanh::lean_inc(v_snap_x3f_2437_);
                        crate::leanh::lean_inc(v_currMacroScope_2436_);
                        crate::leanh::lean_inc(v_quotContext_x3f_2435_);
                        crate::leanh::lean_inc(v_macroStack_2434_);
                        crate::leanh::lean_inc(v_cmdPos_2433_);
                        crate::leanh::lean_inc(v_currRecDepth_2432_);
                        crate::leanh::lean_inc(v_fileMap_2431_);
                        crate::leanh::lean_inc(v_fileName_2430_);
                        crate::leanh::lean_dec(v___y_2425_);
                        v___x_2441_ = crate::leanh::lean_box(0);
                        v_isShared_2442_ = v_isSharedCheck_2458_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2425_);
                    crate::leanh::lean_dec_ref(v_alts_2424_);
                    crate::leanh::lean_dec(v_attrKind_2422_);
                    crate::leanh::lean_dec(v_doc_x3f_2420_);
                    crate::leanh::lean_dec(v___x_2419_);
                    return v___x_2428_;
                }
            }
            1 => {
                v_ref_2443_ = l_Lean_replaceRef(v___x_2418_, v_a_2429_);
                crate::leanh::lean_dec(v_a_2429_);
                if v_isShared_2442_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2441_, 7, v_ref_2443_);
                    v___x_2445_ = v___x_2441_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_fileName_2430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_fileMap_2431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_currRecDepth_2432_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_cmdPos_2433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_macroStack_2434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_quotContext_x3f_2435_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_currMacroScope_2436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_ref_2443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_snap_x3f_2437_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2457_, 9, v_cancelTk_x3f_2438_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2457_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_2439_,
                    );
                    v___x_2445_ = v_reuseFailAlloc_2457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2446_ =
                    l_Lean_Elab_Command_resolveSyntaxKind(v___x_2419_, v___x_2445_, v___y_2426_);
                if crate::leanh::lean_obj_tag(v___x_2446_) == 0 {
                    v_a_2447_ = crate::leanh::lean_ctor_get(v___x_2446_, 0);
                    crate::leanh::lean_inc(v_a_2447_);
                    crate::leanh::lean_dec_ref_known(v___x_2446_, 1);
                    v___x_2448_ = l_Lean_Elab_Command_elabMacroRulesAux(
                        v_doc_x3f_2420_,
                        v_attrs_x3f_2421_,
                        v_attrKind_2422_,
                        v_tk_2423_,
                        v_a_2447_,
                        v_alts_2424_,
                        v___x_2445_,
                        v___y_2426_,
                    );
                    crate::leanh::lean_dec_ref(v___x_2445_);
                    return v___x_2448_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_2445_);
                    crate::leanh::lean_dec_ref(v_alts_2424_);
                    crate::leanh::lean_dec(v_attrKind_2422_);
                    crate::leanh::lean_dec(v_doc_x3f_2420_);
                    v_a_2449_ = crate::leanh::lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2456_ = (!crate::leanh::lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2456_ == 0 {
                        v___x_2451_ = v___x_2446_;
                        v_isShared_2452_ = v_isSharedCheck_2456_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2449_);
                        crate::leanh::lean_dec(v___x_2446_);
                        v___x_2451_ = crate::leanh::lean_box(0);
                        v_isShared_2452_ = v_isSharedCheck_2456_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2452_ == 0 {
                    v___x_2454_ = v___x_2451_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
                    v___x_2454_ = v_reuseFailAlloc_2455_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__0___boxed(
    mut v___x_2460_: *mut crate::leanh::LeanObject,
    mut v___x_2461_: *mut crate::leanh::LeanObject,
    mut v_doc_x3f_2462_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_2463_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2464_: *mut crate::leanh::LeanObject,
    mut v_tk_2465_: *mut crate::leanh::LeanObject,
    mut v_alts_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
    mut v___y_2469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2470_ = l_Lean_Elab_Command_elabMacroRules___lam__0(
        v___x_2460_,
        v___x_2461_,
        v_doc_x3f_2462_,
        v_attrs_x3f_2463_,
        v_attrKind_2464_,
        v_tk_2465_,
        v_alts_2466_,
        v___y_2467_,
        v___y_2468_,
    );
    crate::leanh::lean_dec(v___y_2468_);
    crate::leanh::lean_dec(v_tk_2465_);
    crate::leanh::lean_dec(v_attrs_x3f_2463_);
    crate::leanh::lean_dec(v___x_2460_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__5(
    mut v___x_2474_: *mut crate::leanh::LeanObject,
    mut v___x_2475_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2476_: *mut crate::leanh::LeanObject,
    mut v___x_2477_: *mut crate::leanh::LeanObject,
    mut v___x_2478_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_2479_: *mut crate::leanh::LeanObject,
    mut v___x_2480_: *mut crate::leanh::LeanObject,
    mut v___x_2481_: *mut crate::leanh::LeanObject,
    mut v___x_2482_: *mut crate::leanh::LeanObject,
    mut v_doc_x3f_2483_: *mut crate::leanh::LeanObject,
    mut v_kind_x3f_2484_: *mut crate::leanh::LeanObject,
    mut v_alts_2485_: *mut crate::leanh::LeanObject,
    mut v___y_2486_: *mut crate::leanh::LeanObject,
    mut v___y_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v_quotContext_x3f_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: u8 = 0;
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___y_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_unused_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_a_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2489_ = l_Lean_Elab_Command_getRef___redArg(v___y_2486_);
                if crate::leanh::lean_obj_tag(v___x_2489_) == 0 {
                    v_a_2490_ = crate::leanh::lean_ctor_get(v___x_2489_, 0);
                    crate::leanh::lean_inc(v_a_2490_);
                    crate::leanh::lean_dec_ref_known(v___x_2489_, 1);
                    v___x_2491_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2486_);
                    if crate::leanh::lean_obj_tag(v___x_2491_) == 0 {
                        v_isSharedCheck_2559_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2559_ == 0 {
                            v_unused_2560_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                            crate::leanh::lean_dec(v_unused_2560_);
                            v___x_2493_ = v___x_2491_;
                            v_isShared_2494_ = v_isSharedCheck_2559_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2491_);
                            v___x_2493_ = crate::leanh::lean_box(0);
                            v_isShared_2494_ = v_isSharedCheck_2559_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2490_);
                        crate::leanh::lean_dec(v_kind_x3f_2484_);
                        crate::leanh::lean_dec(v_doc_x3f_2483_);
                        crate::leanh::lean_dec_ref(v___x_2482_);
                        crate::leanh::lean_dec_ref(v___x_2481_);
                        crate::leanh::lean_dec_ref(v___x_2480_);
                        crate::leanh::lean_dec_ref(v___x_2477_);
                        crate::leanh::lean_dec(v_attrKind_2476_);
                        crate::leanh::lean_dec(v___x_2475_);
                        crate::leanh::lean_dec(v___x_2474_);
                        v_a_2561_ = crate::leanh::lean_ctor_get(v___x_2491_, 0);
                        v_isSharedCheck_2568_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2568_ == 0 {
                            v___x_2563_ = v___x_2491_;
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2561_);
                            crate::leanh::lean_dec(v___x_2491_);
                            v___x_2563_ = crate::leanh::lean_box(0);
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_kind_x3f_2484_);
                    crate::leanh::lean_dec(v_doc_x3f_2483_);
                    crate::leanh::lean_dec_ref(v___x_2482_);
                    crate::leanh::lean_dec_ref(v___x_2481_);
                    crate::leanh::lean_dec_ref(v___x_2480_);
                    crate::leanh::lean_dec_ref(v___x_2477_);
                    crate::leanh::lean_dec(v_attrKind_2476_);
                    crate::leanh::lean_dec(v___x_2475_);
                    crate::leanh::lean_dec(v___x_2474_);
                    v_a_2569_ = crate::leanh::lean_ctor_get(v___x_2489_, 0);
                    v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v___x_2489_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2571_ = v___x_2489_;
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2569_);
                        crate::leanh::lean_dec(v___x_2489_);
                        v___x_2571_ = crate::leanh::lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_x3f_2495_ = crate::leanh::lean_ctor_get(v___y_2486_, 5);
                v___x_2496_ = 0;
                v___x_2497_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2496_);
                crate::leanh::lean_dec(v_a_2490_);
                if crate::leanh::lean_obj_tag(v_quotContext_x3f_2495_) == 0 {
                    v___x_2558_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_2487_);
                    crate::leanh::lean_dec_ref(v___x_2558_);
                    state = 6;
                    continue;
                } else {
                    state = 6;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_2503_, 2);
                v___x_2505_ = l_Array_append___redArg(v___y_2503_, v___y_2504_);
                crate::leanh::lean_dec_ref(v___y_2504_);
                crate::leanh::lean_inc_n(v___y_2502_, 2);
                crate::leanh::lean_inc_n(v___x_2497_, 3);
                v___x_2506_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2497_);
                crate::leanh::lean_ctor_set(v___x_2506_, 1, v___y_2502_);
                crate::leanh::lean_ctor_set(v___x_2506_, 2, v___x_2505_);
                v___x_2507_ = l_Array_append___redArg(v___y_2503_, v_alts_2485_);
                v___x_2508_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2497_);
                crate::leanh::lean_ctor_set(v___x_2508_, 1, v___y_2502_);
                crate::leanh::lean_ctor_set(v___x_2508_, 2, v___x_2507_);
                v___x_2509_ = l_Lean_Syntax_node1(v___x_2497_, v___x_2474_, v___x_2508_);
                v___x_2510_ = l_Lean_Syntax_node6(
                    v___x_2497_,
                    v___x_2475_,
                    v___y_2499_,
                    v___y_2501_,
                    v_attrKind_2476_,
                    v___y_2500_,
                    v___x_2506_,
                    v___x_2509_,
                );
                if v_isShared_2494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2510_);
                    v___x_2512_ = v___x_2493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2513_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
                    v___x_2512_ = v_reuseFailAlloc_2513_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2512_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_2517_);
                v___x_2519_ = l_Array_append___redArg(v___y_2517_, v___y_2518_);
                crate::leanh::lean_dec_ref(v___y_2518_);
                crate::leanh::lean_inc(v___y_2516_);
                crate::leanh::lean_inc_n(v___x_2497_, 2);
                v___x_2520_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2497_);
                crate::leanh::lean_ctor_set(v___x_2520_, 1, v___y_2516_);
                crate::leanh::lean_ctor_set(v___x_2520_, 2, v___x_2519_);
                v___x_2521_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2521_, 0, v___x_2497_);
                crate::leanh::lean_ctor_set(v___x_2521_, 1, v___x_2477_);
                if crate::leanh::lean_obj_tag(v_kind_x3f_2484_) == 0 {
                    v___x_2522_ = lean_mk_empty_array_with_capacity(v___x_2478_);
                    v___y_2499_ = v___y_2515_;
                    v___y_2500_ = v___x_2521_;
                    v___y_2501_ = v___x_2520_;
                    v___y_2502_ = v___y_2516_;
                    v___y_2503_ = v___y_2517_;
                    v___y_2504_ = v___x_2522_;
                    state = 2;
                    continue;
                } else {
                    v_val_2523_ = crate::leanh::lean_ctor_get(v_kind_x3f_2484_, 0);
                    crate::leanh::lean_inc(v_val_2523_);
                    crate::leanh::lean_dec_ref_known(v_kind_x3f_2484_, 1);
                    v___x_2524_ = lean_mk_syntax_ident(v_val_2523_);
                    v___x_2525_ = l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0;
                    crate::leanh::lean_inc_n(v___x_2497_, 4);
                    v___x_2526_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2526_, 1, v___x_2525_);
                    v___x_2527_ = l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1;
                    v___x_2528_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2528_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2528_, 1, v___x_2527_);
                    v___x_2529_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
                    v___x_2530_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2530_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                    v___x_2531_ = l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2;
                    v___x_2532_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2532_, 1, v___x_2531_);
                    v___x_2533_ = l_Array_mkArray5___redArg(
                        v___x_2526_,
                        v___x_2528_,
                        v___x_2530_,
                        v___x_2524_,
                        v___x_2532_,
                    );
                    v___y_2499_ = v___y_2515_;
                    v___y_2500_ = v___x_2521_;
                    v___y_2501_ = v___x_2520_;
                    v___y_2502_ = v___y_2516_;
                    v___y_2503_ = v___y_2517_;
                    v___y_2504_ = v___x_2533_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_2536_);
                v___x_2538_ = l_Array_append___redArg(v___y_2536_, v___y_2537_);
                crate::leanh::lean_dec_ref(v___y_2537_);
                crate::leanh::lean_inc(v___y_2535_);
                crate::leanh::lean_inc(v___x_2497_);
                v___x_2539_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2539_, 0, v___x_2497_);
                crate::leanh::lean_ctor_set(v___x_2539_, 1, v___y_2535_);
                crate::leanh::lean_ctor_set(v___x_2539_, 2, v___x_2538_);
                if crate::leanh::lean_obj_tag(v_attrs_x3f_2479_) == 1 {
                    v_val_2540_ = crate::leanh::lean_ctor_get(v_attrs_x3f_2479_, 0);
                    v___x_2541_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__0;
                    v___x_2542_ =
                        l_Lean_Name_mkStr4(v___x_2480_, v___x_2481_, v___x_2482_, v___x_2541_);
                    v___x_2543_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
                    crate::leanh::lean_inc_n(v___x_2497_, 4);
                    v___x_2544_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2544_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2544_, 1, v___x_2543_);
                    crate::leanh::lean_inc_ref(v___y_2536_);
                    v___x_2545_ = l_Array_append___redArg(v___y_2536_, v_val_2540_);
                    crate::leanh::lean_inc(v___y_2535_);
                    v___x_2546_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2546_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2546_, 1, v___y_2535_);
                    crate::leanh::lean_ctor_set(v___x_2546_, 2, v___x_2545_);
                    v___x_2547_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
                    v___x_2548_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2548_, 0, v___x_2497_);
                    crate::leanh::lean_ctor_set(v___x_2548_, 1, v___x_2547_);
                    v___x_2549_ = l_Lean_Syntax_node3(
                        v___x_2497_,
                        v___x_2542_,
                        v___x_2544_,
                        v___x_2546_,
                        v___x_2548_,
                    );
                    v___x_2550_ = l_Array_mkArray1___redArg(v___x_2549_);
                    v___y_2515_ = v___x_2539_;
                    v___y_2516_ = v___y_2535_;
                    v___y_2517_ = v___y_2536_;
                    v___y_2518_ = v___x_2550_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_2482_);
                    crate::leanh::lean_dec_ref(v___x_2481_);
                    crate::leanh::lean_dec_ref(v___x_2480_);
                    v___x_2551_ = lean_mk_empty_array_with_capacity(v___x_2478_);
                    v___y_2515_ = v___x_2539_;
                    v___y_2516_ = v___y_2535_;
                    v___y_2517_ = v___y_2536_;
                    v___y_2518_ = v___x_2551_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_2553_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                v___x_2554_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                if crate::leanh::lean_obj_tag(v_doc_x3f_2483_) == 1 {
                    v_val_2555_ = crate::leanh::lean_ctor_get(v_doc_x3f_2483_, 0);
                    crate::leanh::lean_inc(v_val_2555_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_2483_, 1);
                    v___x_2556_ = l_Array_mkArray1___redArg(v_val_2555_);
                    v___y_2535_ = v___x_2553_;
                    v___y_2536_ = v___x_2554_;
                    v___y_2537_ = v___x_2556_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_2483_);
                    v___x_2557_ = lean_mk_empty_array_with_capacity(v___x_2478_);
                    v___y_2535_ = v___x_2553_;
                    v___y_2536_ = v___x_2554_;
                    v___y_2537_ = v___x_2557_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                if v_isShared_2564_ == 0 {
                    v___x_2566_ = v___x_2563_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
                    v___x_2566_ = v_reuseFailAlloc_2567_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2566_;
            }
            9 => {
                if v_isShared_2572_ == 0 {
                    v___x_2574_ = v___x_2571_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
                    v___x_2574_ = v_reuseFailAlloc_2575_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__5___boxed(
    mut v___x_2577_: *mut crate::leanh::LeanObject,
    mut v___x_2578_: *mut crate::leanh::LeanObject,
    mut v_attrKind_2579_: *mut crate::leanh::LeanObject,
    mut v___x_2580_: *mut crate::leanh::LeanObject,
    mut v___x_2581_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_2582_: *mut crate::leanh::LeanObject,
    mut v___x_2583_: *mut crate::leanh::LeanObject,
    mut v___x_2584_: *mut crate::leanh::LeanObject,
    mut v___x_2585_: *mut crate::leanh::LeanObject,
    mut v_doc_x3f_2586_: *mut crate::leanh::LeanObject,
    mut v_kind_x3f_2587_: *mut crate::leanh::LeanObject,
    mut v_alts_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
    mut v___y_2590_: *mut crate::leanh::LeanObject,
    mut v___y_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2592_ = l_Lean_Elab_Command_elabMacroRules___lam__5(
        v___x_2577_,
        v___x_2578_,
        v_attrKind_2579_,
        v___x_2580_,
        v___x_2581_,
        v_attrs_x3f_2582_,
        v___x_2583_,
        v___x_2584_,
        v___x_2585_,
        v_doc_x3f_2586_,
        v_kind_x3f_2587_,
        v_alts_2588_,
        v___y_2589_,
        v___y_2590_,
    );
    crate::leanh::lean_dec(v___y_2590_);
    crate::leanh::lean_dec_ref(v___y_2589_);
    crate::leanh::lean_dec_ref(v_alts_2588_);
    crate::leanh::lean_dec(v_attrs_x3f_2582_);
    crate::leanh::lean_dec(v___x_2581_);
    return v_res_2592_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__1(
    mut v_stx_2645_: *mut crate::leanh::LeanObject,
    mut v___y_2646_: *mut crate::leanh::LeanObject,
    mut v___y_2647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2650_: u8 = 0;
    let mut v___y_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: u8 = 0;
    let mut v___y_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: u8 = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___y_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: u8 = 0;
    let mut v___y_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v___y_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2786_: u8 = 0;
    let mut v___y_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrKind_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v___x_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: u8 = 0;
    let mut v_alts_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    let mut v_alts_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v_alts_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v_alts_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: u8 = 0;
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v_alts_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: u8 = 0;
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2952_: u8 = 0;
    let mut v___x_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2970_: u8 = 0;
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_a_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_doc_x3f_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4;
                v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5;
                v___x_2660_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0;
                v___x_2661_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1;
                crate::leanh::lean_inc(v_stx_2645_);
                v___x_2662_ = l_Lean_Syntax_isOfKind(v_stx_2645_, v___x_2661_);
                if v___x_2662_ == 0 {
                    crate::leanh::lean_dec(v_stx_2645_);
                    v___x_2728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                    return v___x_2728_;
                } else {
                    v___x_2729_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3038_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2729_);
                    v___x_3039_ = l_Lean_Syntax_isNone(v___x_3038_);
                    if v___x_3039_ == 0 {
                        v___x_3040_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_3038_);
                        v___x_3041_ = l_Lean_Syntax_matchesNull(v___x_3038_, v___x_3040_);
                        if v___x_3041_ == 0 {
                            crate::leanh::lean_dec(v___x_3038_);
                            crate::leanh::lean_dec(v_stx_2645_);
                            v___x_3042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_3042_;
                        } else {
                            v_doc_x3f_3043_ = l_Lean_Syntax_getArg(v___x_3038_, v___x_2729_);
                            crate::leanh::lean_dec(v___x_3038_);
                            v___x_3044_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17;
                            crate::leanh::lean_inc(v_doc_x3f_3043_);
                            v___x_3045_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3043_, v___x_3044_);
                            if v___x_3045_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_3043_);
                                crate::leanh::lean_dec(v_stx_2645_);
                                v___x_3046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                                return v___x_3046_;
                            } else {
                                v___x_3047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3047_, 0, v_doc_x3f_3043_);
                                v_doc_x3f_3022_ = v___x_3047_;
                                v___y_3023_ = v___y_2646_;
                                v___y_3024_ = v___y_2647_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3038_);
                        v___x_3048_ = crate::leanh::lean_box(0);
                        v_doc_x3f_3022_ = v___x_3048_;
                        v___y_3023_ = v___y_2646_;
                        v___y_3024_ = v___y_2647_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_2655_ == 0 {
                    v___x_2656_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_2653_, v___y_2652_, v___y_2654_, v___y_2651_);
                    return v___x_2656_;
                } else {
                    v___x_2657_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___y_2653_, v___y_2650_, v___y_2654_, v___y_2651_);
                    return v___x_2657_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_2676_, 3);
                v___x_2679_ = l_Array_append___redArg(v___y_2676_, v___y_2678_);
                crate::leanh::lean_dec_ref(v___y_2678_);
                crate::leanh::lean_inc_n(v___y_2670_, 6);
                crate::leanh::lean_inc_n(v___y_2669_, 17);
                v___x_2680_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2680_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2680_, 1, v___y_2670_);
                crate::leanh::lean_ctor_set(v___x_2680_, 2, v___x_2679_);
                v___x_2681_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_2673_, 2);
                v___x_2682_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2673_, v___x_2681_);
                v___x_2683_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
                v___x_2684_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2684_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2684_, 1, v___x_2683_);
                v___x_2685_ = l_Array_append___redArg(v___y_2676_, v___y_2671_);
                crate::leanh::lean_dec_ref(v___y_2671_);
                v___x_2686_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2686_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2686_, 1, v___y_2670_);
                crate::leanh::lean_ctor_set(v___x_2686_, 2, v___x_2685_);
                v___x_2687_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
                v___x_2688_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2688_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2688_, 1, v___x_2687_);
                v___x_2689_ = l_Lean_Syntax_node3(
                    v___y_2669_,
                    v___x_2682_,
                    v___x_2684_,
                    v___x_2686_,
                    v___x_2688_,
                );
                v___x_2690_ = l_Lean_Syntax_node1(v___y_2669_, v___y_2670_, v___x_2689_);
                crate::leanh::lean_inc_ref(v___y_2667_);
                v___x_2691_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2691_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2691_, 1, v___y_2667_);
                v___x_2692_ = l_Lean_TSyntax_getId(v___y_2664_);
                v___x_2693_ = l_Lean_mkIdentFrom(v___y_2668_, v___x_2692_, v___x_2662_);
                crate::leanh::lean_dec(v___y_2668_);
                v___x_2694_ =
                    l_Lean_Syntax_node2(v___y_2669_, v___y_2670_, v___x_2693_, v___y_2664_);
                v___x_2695_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
                v___x_2696_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2696_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2696_, 1, v___x_2695_);
                v___x_2697_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8,
                );
                v___x_2698_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
                v___x_2699_ = l_Lean_addMacroScope(v___y_2677_, v___x_2698_, v___y_2672_);
                v___x_2700_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6;
                v___x_2701_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2701_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2701_, 1, v___x_2697_);
                crate::leanh::lean_ctor_set(v___x_2701_, 2, v___x_2699_);
                crate::leanh::lean_ctor_set(v___x_2701_, 3, v___x_2700_);
                v___x_2702_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
                v___x_2703_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2703_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2703_, 1, v___x_2702_);
                v___x_2704_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
                v___x_2705_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2673_, v___x_2704_);
                v___x_2706_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2706_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2706_, 1, v___x_2704_);
                v___x_2707_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7;
                v___x_2708_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2673_, v___x_2707_);
                v___x_2709_ = l_Lean_Syntax_node1(v___y_2669_, v___y_2670_, v___y_2665_);
                v___x_2710_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2710_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2710_, 1, v___y_2670_);
                crate::leanh::lean_ctor_set(v___x_2710_, 2, v___y_2676_);
                v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13;
                v___x_2712_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2712_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2712_, 1, v___x_2711_);
                v___x_2713_ = l_Lean_Syntax_node4(
                    v___y_2669_,
                    v___x_2708_,
                    v___x_2709_,
                    v___x_2710_,
                    v___x_2712_,
                    v___y_2674_,
                );
                v___x_2714_ =
                    l_Lean_Syntax_node2(v___y_2669_, v___x_2705_, v___x_2706_, v___x_2713_);
                v___x_2715_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_2716_ = lean_mk_empty_array_with_capacity(v___x_2715_);
                v___x_2717_ = lean_array_push(v___x_2716_, v___x_2680_);
                v___x_2718_ = lean_array_push(v___x_2717_, v___x_2690_);
                v___x_2719_ = lean_array_push(v___x_2718_, v___y_2675_);
                v___x_2720_ = lean_array_push(v___x_2719_, v___x_2691_);
                v___x_2721_ = lean_array_push(v___x_2720_, v___x_2694_);
                v___x_2722_ = lean_array_push(v___x_2721_, v___x_2696_);
                v___x_2723_ = lean_array_push(v___x_2722_, v___x_2701_);
                v___x_2724_ = lean_array_push(v___x_2723_, v___x_2703_);
                v___x_2725_ = lean_array_push(v___x_2724_, v___x_2714_);
                crate::leanh::lean_inc(v___y_2666_);
                v___x_2726_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2726_, 0, v___y_2669_);
                crate::leanh::lean_ctor_set(v___x_2726_, 1, v___y_2666_);
                crate::leanh::lean_ctor_set(v___x_2726_, 2, v___x_2725_);
                v___x_2727_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2727_, 0, v___x_2726_);
                return v___x_2727_;
            }
            3 => {
                v___x_2743_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__31;
                v___x_2744_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__32;
                v___x_2745_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                if crate::leanh::lean_obj_tag(v___y_2737_) == 1 {
                    v_val_2746_ = crate::leanh::lean_ctor_get(v___y_2737_, 0);
                    crate::leanh::lean_inc(v_val_2746_);
                    crate::leanh::lean_dec_ref_known(v___y_2737_, 1);
                    v___x_2747_ = l_Array_mkArray1___redArg(v_val_2746_);
                    v___y_2664_ = v___y_2731_;
                    v___y_2665_ = v___y_2734_;
                    v___y_2666_ = v___x_2744_;
                    v___y_2667_ = v___x_2743_;
                    v___y_2668_ = v___y_2739_;
                    v___y_2669_ = v___y_2740_;
                    v___y_2670_ = v___y_2741_;
                    v___y_2671_ = v___y_2733_;
                    v___y_2672_ = v___y_2732_;
                    v___y_2673_ = v___y_2735_;
                    v___y_2674_ = v___y_2736_;
                    v___y_2675_ = v___y_2738_;
                    v___y_2676_ = v___x_2745_;
                    v___y_2677_ = v_a_2742_;
                    v___y_2678_ = v___x_2747_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_2737_);
                    v___x_2748_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__33;
                    v___y_2664_ = v___y_2731_;
                    v___y_2665_ = v___y_2734_;
                    v___y_2666_ = v___x_2744_;
                    v___y_2667_ = v___x_2743_;
                    v___y_2668_ = v___y_2739_;
                    v___y_2669_ = v___y_2740_;
                    v___y_2670_ = v___y_2741_;
                    v___y_2671_ = v___y_2733_;
                    v___y_2672_ = v___y_2732_;
                    v___y_2673_ = v___y_2735_;
                    v___y_2674_ = v___y_2736_;
                    v___y_2675_ = v___y_2738_;
                    v___y_2676_ = v___x_2745_;
                    v___y_2677_ = v_a_2742_;
                    v___y_2678_ = v___x_2748_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                v___x_2763_ = l_Lean_Elab_Command_getRef___redArg(v___y_2760_);
                if crate::leanh::lean_obj_tag(v___x_2763_) == 0 {
                    v_a_2764_ = crate::leanh::lean_ctor_get(v___x_2763_, 0);
                    crate::leanh::lean_inc(v_a_2764_);
                    crate::leanh::lean_dec_ref_known(v___x_2763_, 1);
                    v___x_2765_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2760_);
                    crate::leanh::lean_dec_ref(v___y_2760_);
                    if crate::leanh::lean_obj_tag(v___x_2765_) == 0 {
                        v_a_2766_ = crate::leanh::lean_ctor_get(v___x_2765_, 0);
                        crate::leanh::lean_inc(v_a_2766_);
                        crate::leanh::lean_dec_ref_known(v___x_2765_, 1);
                        v___x_2767_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_2761_);
                        v___x_2768_ = l_Lean_SourceInfo_fromRef(v_a_2764_, v___y_2754_);
                        crate::leanh::lean_dec(v_a_2764_);
                        if crate::leanh::lean_obj_tag(v___y_2756_) == 0 {
                            v___x_2769_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_2752_);
                            v_a_2770_ = crate::leanh::lean_ctor_get(v___x_2769_, 0);
                            crate::leanh::lean_inc(v_a_2770_);
                            crate::leanh::lean_dec_ref(v___x_2769_);
                            v___y_2731_ = v___y_2750_;
                            v___y_2732_ = v_a_2766_;
                            v___y_2733_ = v___y_2762_;
                            v___y_2734_ = v___y_2751_;
                            v___y_2735_ = v___y_2757_;
                            v___y_2736_ = v___y_2758_;
                            v___y_2737_ = v___y_2759_;
                            v___y_2738_ = v___x_2767_;
                            v___y_2739_ = v___y_2753_;
                            v___y_2740_ = v___x_2768_;
                            v___y_2741_ = v___y_2755_;
                            v_a_2742_ = v_a_2770_;
                            state = 3;
                            continue;
                        } else {
                            v_val_2771_ = crate::leanh::lean_ctor_get(v___y_2756_, 0);
                            crate::leanh::lean_inc(v_val_2771_);
                            v___y_2731_ = v___y_2750_;
                            v___y_2732_ = v_a_2766_;
                            v___y_2733_ = v___y_2762_;
                            v___y_2734_ = v___y_2751_;
                            v___y_2735_ = v___y_2757_;
                            v___y_2736_ = v___y_2758_;
                            v___y_2737_ = v___y_2759_;
                            v___y_2738_ = v___x_2767_;
                            v___y_2739_ = v___y_2753_;
                            v___y_2740_ = v___x_2768_;
                            v___y_2741_ = v___y_2755_;
                            v_a_2742_ = v_val_2771_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2764_);
                        crate::leanh::lean_dec_ref(v___y_2762_);
                        crate::leanh::lean_dec(v___y_2761_);
                        crate::leanh::lean_dec(v___y_2759_);
                        crate::leanh::lean_dec(v___y_2758_);
                        crate::leanh::lean_dec_ref(v___y_2757_);
                        crate::leanh::lean_dec(v___y_2753_);
                        crate::leanh::lean_dec(v___y_2751_);
                        crate::leanh::lean_dec(v___y_2750_);
                        v_a_2772_ = crate::leanh::lean_ctor_get(v___x_2765_, 0);
                        v_isSharedCheck_2779_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2765_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v___x_2774_ = v___x_2765_;
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2772_);
                            crate::leanh::lean_dec(v___x_2765_);
                            v___x_2774_ = crate::leanh::lean_box(0);
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2762_);
                    crate::leanh::lean_dec(v___y_2761_);
                    crate::leanh::lean_dec_ref(v___y_2760_);
                    crate::leanh::lean_dec(v___y_2759_);
                    crate::leanh::lean_dec(v___y_2758_);
                    crate::leanh::lean_dec_ref(v___y_2757_);
                    crate::leanh::lean_dec(v___y_2753_);
                    crate::leanh::lean_dec(v___y_2751_);
                    crate::leanh::lean_dec(v___y_2750_);
                    return v___x_2763_;
                }
            }
            5 => {
                if v_isShared_2775_ == 0 {
                    v___x_2777_ = v___x_2774_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2778_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2777_;
            }
            7 => {
                v___x_2796_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__34;
                crate::leanh::lean_inc_ref(v___y_2790_);
                v___x_2797_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2790_, v___x_2796_);
                v___x_2798_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__37;
                v___x_2799_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__38;
                crate::leanh::lean_inc_n(v___y_2793_, 2);
                v___x_2800_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2800_, 0, v___y_2793_);
                crate::leanh::lean_ctor_set(v___x_2800_, 1, v___x_2798_);
                crate::leanh::lean_inc(v___y_2781_);
                v___x_2801_ =
                    l_Lean_Syntax_node2(v___y_2793_, v___x_2799_, v___x_2800_, v___y_2781_);
                crate::leanh::lean_inc(v___y_2795_);
                v___x_2802_ =
                    l_Lean_Syntax_node2(v___y_2793_, v___x_2797_, v___y_2795_, v___x_2801_);
                if crate::leanh::lean_obj_tag(v___y_2787_) == 0 {
                    v___x_2803_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2804_ = lean_mk_empty_array_with_capacity(v___y_2783_);
                    v___x_2805_ = lean_array_push(v___x_2804_, v___x_2802_);
                    v___x_2806_ = l_Lean_Syntax_SepArray_ofElems(v___x_2803_, v___x_2805_);
                    crate::leanh::lean_dec_ref(v___x_2805_);
                    v___y_2750_ = v___y_2781_;
                    v___y_2751_ = v___y_2782_;
                    v___y_2752_ = v___y_2784_;
                    v___y_2753_ = v___y_2785_;
                    v___y_2754_ = v___y_2786_;
                    v___y_2755_ = v___y_2788_;
                    v___y_2756_ = v___y_2789_;
                    v___y_2757_ = v___y_2790_;
                    v___y_2758_ = v___y_2791_;
                    v___y_2759_ = v___y_2792_;
                    v___y_2760_ = v___y_2794_;
                    v___y_2761_ = v___y_2795_;
                    v___y_2762_ = v___x_2806_;
                    state = 4;
                    continue;
                } else {
                    v_val_2807_ = crate::leanh::lean_ctor_get(v___y_2787_, 0);
                    crate::leanh::lean_inc(v_val_2807_);
                    crate::leanh::lean_dec_ref_known(v___y_2787_, 1);
                    v___x_2808_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2809_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_2807_);
                    crate::leanh::lean_dec(v_val_2807_);
                    v___x_2810_ = lean_array_push(v___x_2809_, v___x_2802_);
                    v___x_2811_ = l_Lean_Syntax_SepArray_ofElems(v___x_2808_, v___x_2810_);
                    crate::leanh::lean_dec_ref(v___x_2810_);
                    v___y_2750_ = v___y_2781_;
                    v___y_2751_ = v___y_2782_;
                    v___y_2752_ = v___y_2784_;
                    v___y_2753_ = v___y_2785_;
                    v___y_2754_ = v___y_2786_;
                    v___y_2755_ = v___y_2788_;
                    v___y_2756_ = v___y_2789_;
                    v___y_2757_ = v___y_2790_;
                    v___y_2758_ = v___y_2791_;
                    v___y_2759_ = v___y_2792_;
                    v___y_2760_ = v___y_2794_;
                    v___y_2761_ = v___y_2795_;
                    v___y_2762_ = v___x_2811_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v___x_2818_ = crate::leanh::lean_unsigned_to_nat(2);
                v_attrKind_2819_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2818_);
                v___x_2820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6;
                v___x_2821_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9;
                crate::leanh::lean_inc(v_attrKind_2819_);
                v___x_2822_ = l_Lean_Syntax_isOfKind(v_attrKind_2819_, v___x_2821_);
                if v___x_2822_ == 0 {
                    crate::leanh::lean_dec(v_attrKind_2819_);
                    crate::leanh::lean_dec(v_attrs_x3f_2817_);
                    crate::leanh::lean_dec(v___y_2813_);
                    crate::leanh::lean_dec(v_stx_2645_);
                    v___x_2823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                    return v___x_2823_;
                } else {
                    v___x_2824_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_tk_2825_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2824_);
                    v___x_2826_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2827_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2826_);
                    crate::leanh::lean_inc(v___x_2827_);
                    v___x_2828_ = l_Lean_Syntax_matchesNull(v___x_2827_, v___x_2729_);
                    if v___x_2828_ == 0 {
                        v___x_2829_ = crate::leanh::lean_unsigned_to_nat(5);
                        crate::leanh::lean_inc(v___x_2827_);
                        v___x_2830_ = l_Lean_Syntax_matchesNull(v___x_2827_, v___x_2829_);
                        if v___x_2830_ == 0 {
                            crate::leanh::lean_dec(v___x_2827_);
                            crate::leanh::lean_dec(v_tk_2825_);
                            crate::leanh::lean_dec(v_attrKind_2819_);
                            crate::leanh::lean_dec(v_attrs_x3f_2817_);
                            crate::leanh::lean_dec(v___y_2813_);
                            crate::leanh::lean_dec(v_stx_2645_);
                            v___x_2831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_2831_;
                        } else {
                            v___x_2832_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2829_);
                            crate::leanh::lean_dec(v_stx_2645_);
                            v___x_2833_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10;
                            crate::leanh::lean_inc(v___x_2832_);
                            v___x_2834_ = l_Lean_Syntax_isOfKind(v___x_2832_, v___x_2833_);
                            if v___x_2834_ == 0 {
                                crate::leanh::lean_dec(v___x_2832_);
                                crate::leanh::lean_dec(v___x_2827_);
                                crate::leanh::lean_dec(v_tk_2825_);
                                crate::leanh::lean_dec(v_attrKind_2819_);
                                crate::leanh::lean_dec(v_attrs_x3f_2817_);
                                crate::leanh::lean_dec(v___y_2813_);
                                v___x_2835_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                                return v___x_2835_;
                            } else {
                                v_kind_2836_ = l_Lean_Syntax_getArg(v___x_2827_, v___x_2824_);
                                crate::leanh::lean_dec(v___x_2827_);
                                v___x_2837_ = l_Lean_Syntax_getArg(v___x_2832_, v___x_2729_);
                                crate::leanh::lean_dec(v___x_2832_);
                                crate::leanh::lean_inc(v___x_2837_);
                                v___x_2838_ = l_Lean_Syntax_matchesNull(v___x_2837_, v___y_2816_);
                                if v___x_2838_ == 0 {
                                    v_alts_2839_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                    crate::leanh::lean_dec(v___x_2837_);
                                    v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                    v___x_2841_ = crate::leanh::lean_box(2);
                                    crate::leanh::lean_inc_ref(v_alts_2839_);
                                    v___x_2842_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2842_, 0, v___x_2841_);
                                    crate::leanh::lean_ctor_set(v___x_2842_, 1, v___x_2840_);
                                    crate::leanh::lean_ctor_set(v___x_2842_, 2, v_alts_2839_);
                                    v___x_2843_ = lean_mk_empty_array_with_capacity(v___x_2818_);
                                    crate::leanh::lean_inc(v_tk_2825_);
                                    v___x_2844_ = lean_array_push(v___x_2843_, v_tk_2825_);
                                    v___x_2845_ = lean_array_push(v___x_2844_, v___x_2842_);
                                    v___x_2846_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2846_, 0, v___x_2841_);
                                    crate::leanh::lean_ctor_set(v___x_2846_, 1, v___x_2840_);
                                    crate::leanh::lean_ctor_set(v___x_2846_, 2, v___x_2845_);
                                    v___x_2847_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                    crate::leanh::lean_dec(v_kind_2836_);
                                    crate::leanh::lean_inc(v_attrKind_2819_);
                                    v___f_2848_ = crate::leanh::lean_alloc_closure(
                                        l_Lean_Elab_Command_elabMacroRules___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        10,
                                        7,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2848_, 0, v___x_2846_);
                                    crate::leanh::lean_closure_set(v___f_2848_, 1, v___x_2847_);
                                    crate::leanh::lean_closure_set(v___f_2848_, 2, v___y_2813_);
                                    crate::leanh::lean_closure_set(
                                        v___f_2848_,
                                        3,
                                        v_attrs_x3f_2817_,
                                    );
                                    crate::leanh::lean_closure_set(
                                        v___f_2848_,
                                        4,
                                        v_attrKind_2819_,
                                    );
                                    crate::leanh::lean_closure_set(v___f_2848_, 5, v_tk_2825_);
                                    crate::leanh::lean_closure_set(v___f_2848_, 6, v_alts_2839_);
                                    if v___x_2822_ == 0 {
                                        crate::leanh::lean_dec(v_attrKind_2819_);
                                        v___x_2849_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2848_, v___x_2822_, v___y_2814_, v___y_2815_);
                                        return v___x_2849_;
                                    } else {
                                        v___x_2850_ =
                                            l_Lean_Syntax_getArg(v_attrKind_2819_, v___x_2729_);
                                        crate::leanh::lean_dec(v_attrKind_2819_);
                                        crate::leanh::lean_inc(v___x_2850_);
                                        v___x_2851_ =
                                            l_Lean_Syntax_matchesNull(v___x_2850_, v___y_2816_);
                                        if v___x_2851_ == 0 {
                                            crate::leanh::lean_dec(v___x_2850_);
                                            v___x_2852_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2848_, v___x_2822_, v___y_2814_, v___y_2815_);
                                            return v___x_2852_;
                                        } else {
                                            v___x_2853_ =
                                                l_Lean_Syntax_getArg(v___x_2850_, v___x_2729_);
                                            crate::leanh::lean_dec(v___x_2850_);
                                            v___x_2854_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12;
                                            v___x_2855_ =
                                                l_Lean_Syntax_isOfKind(v___x_2853_, v___x_2854_);
                                            if v___x_2855_ == 0 {
                                                v___x_2856_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2848_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                return v___x_2856_;
                                            } else {
                                                v___x_2857_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2848_, v___x_2838_, v___y_2814_, v___y_2815_);
                                                return v___x_2857_;
                                            }
                                        }
                                    }
                                } else {
                                    v___x_2858_ = l_Lean_Syntax_getArg(v___x_2837_, v___x_2729_);
                                    v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8;
                                    crate::leanh::lean_inc(v___x_2858_);
                                    v___x_2860_ = l_Lean_Syntax_isOfKind(v___x_2858_, v___x_2859_);
                                    if v___x_2860_ == 0 {
                                        crate::leanh::lean_dec(v___x_2858_);
                                        v_alts_2861_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                        crate::leanh::lean_dec(v___x_2837_);
                                        v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                        v___x_2863_ = crate::leanh::lean_box(2);
                                        crate::leanh::lean_inc_ref(v_alts_2861_);
                                        v___x_2864_ =
                                            crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2864_, 0, v___x_2863_);
                                        crate::leanh::lean_ctor_set(v___x_2864_, 1, v___x_2862_);
                                        crate::leanh::lean_ctor_set(v___x_2864_, 2, v_alts_2861_);
                                        v___x_2865_ =
                                            lean_mk_empty_array_with_capacity(v___x_2818_);
                                        crate::leanh::lean_inc(v_tk_2825_);
                                        v___x_2866_ = lean_array_push(v___x_2865_, v_tk_2825_);
                                        v___x_2867_ = lean_array_push(v___x_2866_, v___x_2864_);
                                        v___x_2868_ =
                                            crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_2868_, 0, v___x_2863_);
                                        crate::leanh::lean_ctor_set(v___x_2868_, 1, v___x_2862_);
                                        crate::leanh::lean_ctor_set(v___x_2868_, 2, v___x_2867_);
                                        v___x_2869_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                        crate::leanh::lean_dec(v_kind_2836_);
                                        crate::leanh::lean_inc(v_attrKind_2819_);
                                        v___f_2870_ = crate::leanh::lean_alloc_closure(
                                            l_Lean_Elab_Command_elabMacroRules___lam__0___boxed
                                                as *mut core::ffi::c_void,
                                            10,
                                            7,
                                        );
                                        crate::leanh::lean_closure_set(v___f_2870_, 0, v___x_2868_);
                                        crate::leanh::lean_closure_set(v___f_2870_, 1, v___x_2869_);
                                        crate::leanh::lean_closure_set(v___f_2870_, 2, v___y_2813_);
                                        crate::leanh::lean_closure_set(
                                            v___f_2870_,
                                            3,
                                            v_attrs_x3f_2817_,
                                        );
                                        crate::leanh::lean_closure_set(
                                            v___f_2870_,
                                            4,
                                            v_attrKind_2819_,
                                        );
                                        crate::leanh::lean_closure_set(v___f_2870_, 5, v_tk_2825_);
                                        crate::leanh::lean_closure_set(
                                            v___f_2870_,
                                            6,
                                            v_alts_2861_,
                                        );
                                        if v___x_2822_ == 0 {
                                            crate::leanh::lean_dec(v_attrKind_2819_);
                                            v___x_2871_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2870_, v___x_2822_, v___y_2814_, v___y_2815_);
                                            return v___x_2871_;
                                        } else {
                                            v___x_2872_ =
                                                l_Lean_Syntax_getArg(v_attrKind_2819_, v___x_2729_);
                                            crate::leanh::lean_dec(v_attrKind_2819_);
                                            crate::leanh::lean_inc(v___x_2872_);
                                            v___x_2873_ =
                                                l_Lean_Syntax_matchesNull(v___x_2872_, v___y_2816_);
                                            if v___x_2873_ == 0 {
                                                crate::leanh::lean_dec(v___x_2872_);
                                                v___x_2874_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2870_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                return v___x_2874_;
                                            } else {
                                                v___x_2875_ =
                                                    l_Lean_Syntax_getArg(v___x_2872_, v___x_2729_);
                                                crate::leanh::lean_dec(v___x_2872_);
                                                v___x_2876_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12;
                                                v___x_2877_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2875_,
                                                    v___x_2876_,
                                                );
                                                if v___x_2877_ == 0 {
                                                    v___x_2878_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2870_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                    return v___x_2878_;
                                                } else {
                                                    v___x_2879_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2870_, v___x_2860_, v___y_2814_, v___y_2815_);
                                                    return v___x_2879_;
                                                }
                                            }
                                        }
                                    } else {
                                        v___x_2880_ =
                                            l_Lean_Syntax_getArg(v___x_2858_, v___y_2816_);
                                        crate::leanh::lean_inc(v___x_2880_);
                                        v___x_2881_ =
                                            l_Lean_Syntax_matchesNull(v___x_2880_, v___y_2816_);
                                        if v___x_2881_ == 0 {
                                            crate::leanh::lean_dec(v___x_2880_);
                                            crate::leanh::lean_dec(v___x_2858_);
                                            v_alts_2882_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                            crate::leanh::lean_dec(v___x_2837_);
                                            v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                            v___x_2884_ = crate::leanh::lean_box(2);
                                            crate::leanh::lean_inc_ref(v_alts_2882_);
                                            v___x_2885_ =
                                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2885_,
                                                0,
                                                v___x_2884_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2885_,
                                                1,
                                                v___x_2883_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2885_,
                                                2,
                                                v_alts_2882_,
                                            );
                                            v___x_2886_ =
                                                lean_mk_empty_array_with_capacity(v___x_2818_);
                                            crate::leanh::lean_inc(v_tk_2825_);
                                            v___x_2887_ = lean_array_push(v___x_2886_, v_tk_2825_);
                                            v___x_2888_ = lean_array_push(v___x_2887_, v___x_2885_);
                                            v___x_2889_ =
                                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2889_,
                                                0,
                                                v___x_2884_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2889_,
                                                1,
                                                v___x_2883_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2889_,
                                                2,
                                                v___x_2888_,
                                            );
                                            v___x_2890_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                            crate::leanh::lean_dec(v_kind_2836_);
                                            crate::leanh::lean_inc(v_attrKind_2819_);
                                            v___f_2891_ = crate::leanh::lean_alloc_closure(
                                                l_Lean_Elab_Command_elabMacroRules___lam__0___boxed
                                                    as *mut core::ffi::c_void,
                                                10,
                                                7,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                0,
                                                v___x_2889_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                1,
                                                v___x_2890_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                2,
                                                v___y_2813_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                3,
                                                v_attrs_x3f_2817_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                4,
                                                v_attrKind_2819_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                5,
                                                v_tk_2825_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_2891_,
                                                6,
                                                v_alts_2882_,
                                            );
                                            if v___x_2822_ == 0 {
                                                crate::leanh::lean_dec(v_attrKind_2819_);
                                                v___x_2892_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2891_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                return v___x_2892_;
                                            } else {
                                                v___x_2893_ = l_Lean_Syntax_getArg(
                                                    v_attrKind_2819_,
                                                    v___x_2729_,
                                                );
                                                crate::leanh::lean_dec(v_attrKind_2819_);
                                                crate::leanh::lean_inc(v___x_2893_);
                                                v___x_2894_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2893_,
                                                    v___y_2816_,
                                                );
                                                if v___x_2894_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2893_);
                                                    v___x_2895_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2891_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                    return v___x_2895_;
                                                } else {
                                                    v___x_2896_ = l_Lean_Syntax_getArg(
                                                        v___x_2893_,
                                                        v___x_2729_,
                                                    );
                                                    crate::leanh::lean_dec(v___x_2893_);
                                                    v___x_2897_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12;
                                                    v___x_2898_ = l_Lean_Syntax_isOfKind(
                                                        v___x_2896_,
                                                        v___x_2897_,
                                                    );
                                                    if v___x_2898_ == 0 {
                                                        v___x_2899_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2891_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                        return v___x_2899_;
                                                    } else {
                                                        v___x_2900_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2891_, v___x_2881_, v___y_2814_, v___y_2815_);
                                                        return v___x_2900_;
                                                    }
                                                }
                                            }
                                        } else {
                                            v___x_2901_ =
                                                l_Lean_Syntax_getArg(v___x_2880_, v___x_2729_);
                                            crate::leanh::lean_dec(v___x_2880_);
                                            crate::leanh::lean_inc(v___x_2901_);
                                            v___x_2902_ =
                                                l_Lean_Syntax_matchesNull(v___x_2901_, v___y_2816_);
                                            if v___x_2902_ == 0 {
                                                crate::leanh::lean_dec(v___x_2901_);
                                                crate::leanh::lean_dec(v___x_2858_);
                                                v_alts_2903_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                                crate::leanh::lean_dec(v___x_2837_);
                                                v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                                v___x_2905_ = crate::leanh::lean_box(2);
                                                crate::leanh::lean_inc_ref(v_alts_2903_);
                                                v___x_2906_ =
                                                    crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2906_,
                                                    0,
                                                    v___x_2905_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2906_,
                                                    1,
                                                    v___x_2904_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2906_,
                                                    2,
                                                    v_alts_2903_,
                                                );
                                                v___x_2907_ =
                                                    lean_mk_empty_array_with_capacity(v___x_2818_);
                                                crate::leanh::lean_inc(v_tk_2825_);
                                                v___x_2908_ =
                                                    lean_array_push(v___x_2907_, v_tk_2825_);
                                                v___x_2909_ =
                                                    lean_array_push(v___x_2908_, v___x_2906_);
                                                v___x_2910_ =
                                                    crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2910_,
                                                    0,
                                                    v___x_2905_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2910_,
                                                    1,
                                                    v___x_2904_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_2910_,
                                                    2,
                                                    v___x_2909_,
                                                );
                                                v___x_2911_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                                crate::leanh::lean_dec(v_kind_2836_);
                                                crate::leanh::lean_inc(v_attrKind_2819_);
                                                v___f_2912_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed as *mut core::ffi::c_void, 10, 7);
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    0,
                                                    v___x_2910_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    1,
                                                    v___x_2911_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    2,
                                                    v___y_2813_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    3,
                                                    v_attrs_x3f_2817_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    4,
                                                    v_attrKind_2819_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    5,
                                                    v_tk_2825_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_2912_,
                                                    6,
                                                    v_alts_2903_,
                                                );
                                                if v___x_2822_ == 0 {
                                                    crate::leanh::lean_dec(v_attrKind_2819_);
                                                    v___x_2913_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2912_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                    return v___x_2913_;
                                                } else {
                                                    v___x_2914_ = l_Lean_Syntax_getArg(
                                                        v_attrKind_2819_,
                                                        v___x_2729_,
                                                    );
                                                    crate::leanh::lean_dec(v_attrKind_2819_);
                                                    crate::leanh::lean_inc(v___x_2914_);
                                                    v___x_2915_ = l_Lean_Syntax_matchesNull(
                                                        v___x_2914_,
                                                        v___y_2816_,
                                                    );
                                                    if v___x_2915_ == 0 {
                                                        crate::leanh::lean_dec(v___x_2914_);
                                                        v___x_2916_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2912_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                        return v___x_2916_;
                                                    } else {
                                                        v___x_2917_ = l_Lean_Syntax_getArg(
                                                            v___x_2914_,
                                                            v___x_2729_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2914_);
                                                        v___x_2918_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12;
                                                        v___x_2919_ = l_Lean_Syntax_isOfKind(
                                                            v___x_2917_,
                                                            v___x_2918_,
                                                        );
                                                        if v___x_2919_ == 0 {
                                                            v___x_2920_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2912_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                            return v___x_2920_;
                                                        } else {
                                                            v___x_2921_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2912_, v___x_2902_, v___y_2814_, v___y_2815_);
                                                            return v___x_2921_;
                                                        }
                                                    }
                                                }
                                            } else {
                                                v___x_2922_ =
                                                    l_Lean_Syntax_getArg(v___x_2901_, v___x_2729_);
                                                crate::leanh::lean_dec(v___x_2901_);
                                                v___x_2923_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14;
                                                crate::leanh::lean_inc(v___x_2922_);
                                                v___x_2924_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2922_,
                                                    v___x_2923_,
                                                );
                                                if v___x_2924_ == 0 {
                                                    crate::leanh::lean_dec(v___x_2922_);
                                                    crate::leanh::lean_dec(v___x_2858_);
                                                    v_alts_2925_ =
                                                        l_Lean_Syntax_getArgs(v___x_2837_);
                                                    crate::leanh::lean_dec(v___x_2837_);
                                                    v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                                    v___x_2927_ = crate::leanh::lean_box(2);
                                                    crate::leanh::lean_inc_ref(v_alts_2925_);
                                                    v___x_2928_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        3,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2928_,
                                                        0,
                                                        v___x_2927_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2928_,
                                                        1,
                                                        v___x_2926_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2928_,
                                                        2,
                                                        v_alts_2925_,
                                                    );
                                                    v___x_2929_ = lean_mk_empty_array_with_capacity(
                                                        v___x_2818_,
                                                    );
                                                    crate::leanh::lean_inc(v_tk_2825_);
                                                    v___x_2930_ =
                                                        lean_array_push(v___x_2929_, v_tk_2825_);
                                                    v___x_2931_ =
                                                        lean_array_push(v___x_2930_, v___x_2928_);
                                                    v___x_2932_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        3,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2932_,
                                                        0,
                                                        v___x_2927_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2932_,
                                                        1,
                                                        v___x_2926_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_2932_,
                                                        2,
                                                        v___x_2931_,
                                                    );
                                                    v___x_2933_ =
                                                        l_Lean_TSyntax_getId(v_kind_2836_);
                                                    crate::leanh::lean_dec(v_kind_2836_);
                                                    crate::leanh::lean_inc(v_attrKind_2819_);
                                                    v___f_2934_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed as *mut core::ffi::c_void, 10, 7);
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        0,
                                                        v___x_2932_,
                                                    );
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        1,
                                                        v___x_2933_,
                                                    );
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        2,
                                                        v___y_2813_,
                                                    );
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        3,
                                                        v_attrs_x3f_2817_,
                                                    );
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        4,
                                                        v_attrKind_2819_,
                                                    );
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        5,
                                                        v_tk_2825_,
                                                    );
                                                    crate::leanh::lean_closure_set(
                                                        v___f_2934_,
                                                        6,
                                                        v_alts_2925_,
                                                    );
                                                    if v___x_2822_ == 0 {
                                                        crate::leanh::lean_dec(v_attrKind_2819_);
                                                        v___y_2650_ = v___x_2924_;
                                                        v___y_2651_ = v___y_2815_;
                                                        v___y_2652_ = v___x_2902_;
                                                        v___y_2653_ = v___f_2934_;
                                                        v___y_2654_ = v___y_2814_;
                                                        v___y_2655_ = v___x_2924_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_2935_ = l_Lean_Syntax_getArg(
                                                            v_attrKind_2819_,
                                                            v___x_2729_,
                                                        );
                                                        crate::leanh::lean_dec(v_attrKind_2819_);
                                                        crate::leanh::lean_inc(v___x_2935_);
                                                        v___x_2936_ = l_Lean_Syntax_matchesNull(
                                                            v___x_2935_,
                                                            v___y_2816_,
                                                        );
                                                        if v___x_2936_ == 0 {
                                                            crate::leanh::lean_dec(v___x_2935_);
                                                            v___y_2650_ = v___x_2924_;
                                                            v___y_2651_ = v___y_2815_;
                                                            v___y_2652_ = v___x_2902_;
                                                            v___y_2653_ = v___f_2934_;
                                                            v___y_2654_ = v___y_2814_;
                                                            v___y_2655_ = v___x_2924_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            v___x_2937_ = l_Lean_Syntax_getArg(
                                                                v___x_2935_,
                                                                v___x_2729_,
                                                            );
                                                            crate::leanh::lean_dec(v___x_2935_);
                                                            v___x_2938_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12;
                                                            v___x_2939_ = l_Lean_Syntax_isOfKind(
                                                                v___x_2937_,
                                                                v___x_2938_,
                                                            );
                                                            if v___x_2939_ == 0 {
                                                                v___y_2650_ = v___x_2924_;
                                                                v___y_2651_ = v___y_2815_;
                                                                v___y_2652_ = v___x_2902_;
                                                                v___y_2653_ = v___f_2934_;
                                                                v___y_2654_ = v___y_2814_;
                                                                v___y_2655_ = v___x_2924_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                v___x_2940_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2934_, v___x_2924_, v___y_2814_, v___y_2815_);
                                                                return v___x_2940_;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v___x_2837_);
                                                    v___x_2941_ =
                                                        l_Lean_Elab_Command_getRef___redArg(
                                                            v___y_2814_,
                                                        );
                                                    if crate::leanh::lean_obj_tag(v___x_2941_) == 0
                                                    {
                                                        v_a_2942_ = crate::leanh::lean_ctor_get(
                                                            v___x_2941_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_2942_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2941_,
                                                            1,
                                                        );
                                                        v_fileName_2943_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                0,
                                                            );
                                                        v_fileMap_2944_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                1,
                                                            );
                                                        v_currRecDepth_2945_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                2,
                                                            );
                                                        v_cmdPos_2946_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                3,
                                                            );
                                                        v_macroStack_2947_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                4,
                                                            );
                                                        v_quotContext_x3f_2948_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                5,
                                                            );
                                                        v_currMacroScope_2949_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                6,
                                                            );
                                                        v_snap_x3f_2950_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                8,
                                                            );
                                                        v_cancelTk_x3f_2951_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___y_2814_,
                                                                9,
                                                            );
                                                        v_suppressElabErrors_2952_ =
                                                            crate::leanh::lean_ctor_get_uint8(
                                                                v___y_2814_,
                                                                (core::mem::size_of::<
                                                                    *mut crate::leanh::LeanObject,
                                                                >(
                                                                ) * 10)
                                                                    as u32,
                                                            );
                                                        v___x_2953_ = l_Lean_Syntax_getArg(
                                                            v___x_2858_,
                                                            v___x_2824_,
                                                        );
                                                        crate::leanh::lean_dec(v___x_2858_);
                                                        v___x_2954_ =
                                                            lean_mk_empty_array_with_capacity(
                                                                v___x_2818_,
                                                            );
                                                        crate::leanh::lean_inc(v_tk_2825_);
                                                        v___x_2955_ = lean_array_push(
                                                            v___x_2954_,
                                                            v_tk_2825_,
                                                        );
                                                        crate::leanh::lean_inc(v___x_2953_);
                                                        v___x_2956_ = lean_array_push(
                                                            v___x_2955_,
                                                            v___x_2953_,
                                                        );
                                                        v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                                        v___x_2958_ = crate::leanh::lean_box(2);
                                                        v___x_2959_ = crate::leanh::lean_alloc_ctor(
                                                            1,
                                                            3,
                                                            (0) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2959_,
                                                            0,
                                                            v___x_2958_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2959_,
                                                            1,
                                                            v___x_2957_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2959_,
                                                            2,
                                                            v___x_2956_,
                                                        );
                                                        v_ref_2960_ = l_Lean_replaceRef(
                                                            v___x_2959_,
                                                            v_a_2942_,
                                                        );
                                                        crate::leanh::lean_dec(v_a_2942_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_2959_,
                                                            3,
                                                        );
                                                        crate::leanh::lean_inc(
                                                            v_cancelTk_x3f_2951_,
                                                        );
                                                        crate::leanh::lean_inc(v_snap_x3f_2950_);
                                                        crate::leanh::lean_inc(
                                                            v_currMacroScope_2949_,
                                                        );
                                                        crate::leanh::lean_inc(
                                                            v_quotContext_x3f_2948_,
                                                        );
                                                        crate::leanh::lean_inc(v_macroStack_2947_);
                                                        crate::leanh::lean_inc(v_cmdPos_2946_);
                                                        crate::leanh::lean_inc(
                                                            v_currRecDepth_2945_,
                                                        );
                                                        crate::leanh::lean_inc_ref(v_fileMap_2944_);
                                                        crate::leanh::lean_inc_ref(
                                                            v_fileName_2943_,
                                                        );
                                                        v___x_2961_ = crate::leanh::lean_alloc_ctor(
                                                            0,
                                                            10,
                                                            (1) as u32,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            0,
                                                            v_fileName_2943_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            1,
                                                            v_fileMap_2944_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            2,
                                                            v_currRecDepth_2945_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            3,
                                                            v_cmdPos_2946_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            4,
                                                            v_macroStack_2947_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            5,
                                                            v_quotContext_x3f_2948_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            6,
                                                            v_currMacroScope_2949_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            7,
                                                            v_ref_2960_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            8,
                                                            v_snap_x3f_2950_,
                                                        );
                                                        crate::leanh::lean_ctor_set(
                                                            v___x_2961_,
                                                            9,
                                                            v_cancelTk_x3f_2951_,
                                                        );
                                                        crate::leanh::lean_ctor_set_uint8(
                                                            v___x_2961_,
                                                            (core::mem::size_of::<
                                                                *mut crate::leanh::LeanObject,
                                                            >(
                                                            ) * 10)
                                                                as u32,
                                                            v_suppressElabErrors_2952_,
                                                        );
                                                        v___x_2962_ =
                                                            l_Lean_Elab_Command_getRef___redArg(
                                                                v___x_2961_,
                                                            );
                                                        if crate::leanh::lean_obj_tag(v___x_2962_)
                                                            == 0
                                                        {
                                                            v_a_2963_ = crate::leanh::lean_ctor_get(
                                                                v___x_2962_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_2963_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_2962_,
                                                                1,
                                                            );
                                                            v___x_2964_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_2961_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_2964_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_2964_,
                                                                    1,
                                                                );
                                                                v___x_2965_ =
                                                                    l_Lean_SourceInfo_fromRef(
                                                                        v_a_2963_,
                                                                        v___x_2828_,
                                                                    );
                                                                crate::leanh::lean_dec(v_a_2963_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v_quotContext_x3f_2948_,
                                                                ) == 0
                                                                {
                                                                    v___x_2966_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_2815_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___x_2966_,
                                                                    );
                                                                    v___y_2781_ = v_kind_2836_;
                                                                    v___y_2782_ = v___x_2922_;
                                                                    v___y_2783_ = v___y_2816_;
                                                                    v___y_2784_ = v___y_2815_;
                                                                    v___y_2785_ = v_tk_2825_;
                                                                    v___y_2786_ = v___x_2828_;
                                                                    v___y_2787_ = v_attrs_x3f_2817_;
                                                                    v___y_2788_ = v___x_2957_;
                                                                    v___y_2789_ =
                                                                        v_quotContext_x3f_2948_;
                                                                    v___y_2790_ = v___x_2820_;
                                                                    v___y_2791_ = v___x_2953_;
                                                                    v___y_2792_ = v___y_2813_;
                                                                    v___y_2793_ = v___x_2965_;
                                                                    v___y_2794_ = v___x_2961_;
                                                                    v___y_2795_ = v_attrKind_2819_;
                                                                    state = 7;
                                                                    continue;
                                                                } else {
                                                                    v___y_2781_ = v_kind_2836_;
                                                                    v___y_2782_ = v___x_2922_;
                                                                    v___y_2783_ = v___y_2816_;
                                                                    v___y_2784_ = v___y_2815_;
                                                                    v___y_2785_ = v_tk_2825_;
                                                                    v___y_2786_ = v___x_2828_;
                                                                    v___y_2787_ = v_attrs_x3f_2817_;
                                                                    v___y_2788_ = v___x_2957_;
                                                                    v___y_2789_ =
                                                                        v_quotContext_x3f_2948_;
                                                                    v___y_2790_ = v___x_2820_;
                                                                    v___y_2791_ = v___x_2953_;
                                                                    v___y_2792_ = v___y_2813_;
                                                                    v___y_2793_ = v___x_2965_;
                                                                    v___y_2794_ = v___x_2961_;
                                                                    v___y_2795_ = v_attrKind_2819_;
                                                                    state = 7;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_2963_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_2961_,
                                                                    10,
                                                                );
                                                                crate::leanh::lean_dec(v___x_2953_);
                                                                crate::leanh::lean_dec(v___x_2922_);
                                                                crate::leanh::lean_dec(
                                                                    v_kind_2836_,
                                                                );
                                                                crate::leanh::lean_dec(v_tk_2825_);
                                                                crate::leanh::lean_dec(
                                                                    v_attrKind_2819_,
                                                                );
                                                                crate::leanh::lean_dec(
                                                                    v_attrs_x3f_2817_,
                                                                );
                                                                crate::leanh::lean_dec(v___y_2813_);
                                                                v_a_2967_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2964_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2974_ = (!crate::leanh::lean_is_exclusive(v___x_2964_)) as u8;
                                                                if v_isSharedCheck_2974_ == 0 {
                                                                    v___x_2969_ = v___x_2964_;
                                                                    v_isShared_2970_ =
                                                                        v_isSharedCheck_2974_;
                                                                    state = 9;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2967_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_2964_,
                                                                    );
                                                                    v___x_2969_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_2970_ =
                                                                        v_isSharedCheck_2974_;
                                                                    state = 9;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_2961_,
                                                                10,
                                                            );
                                                            crate::leanh::lean_dec(v___x_2953_);
                                                            crate::leanh::lean_dec(v___x_2922_);
                                                            crate::leanh::lean_dec(v_kind_2836_);
                                                            crate::leanh::lean_dec(v_tk_2825_);
                                                            crate::leanh::lean_dec(
                                                                v_attrKind_2819_,
                                                            );
                                                            crate::leanh::lean_dec(
                                                                v_attrs_x3f_2817_,
                                                            );
                                                            crate::leanh::lean_dec(v___y_2813_);
                                                            return v___x_2962_;
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_2922_);
                                                        crate::leanh::lean_dec(v___x_2858_);
                                                        crate::leanh::lean_dec(v_kind_2836_);
                                                        crate::leanh::lean_dec(v_tk_2825_);
                                                        crate::leanh::lean_dec(v_attrKind_2819_);
                                                        crate::leanh::lean_dec(v_attrs_x3f_2817_);
                                                        crate::leanh::lean_dec(v___y_2813_);
                                                        return v___x_2941_;
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2827_);
                        v___x_2975_ = crate::leanh::lean_unsigned_to_nat(5);
                        v___x_2976_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2975_);
                        crate::leanh::lean_dec(v_stx_2645_);
                        v___x_2977_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10;
                        crate::leanh::lean_inc(v___x_2976_);
                        v___x_2978_ = l_Lean_Syntax_isOfKind(v___x_2976_, v___x_2977_);
                        if v___x_2978_ == 0 {
                            crate::leanh::lean_dec(v___x_2976_);
                            crate::leanh::lean_dec(v_tk_2825_);
                            crate::leanh::lean_dec(v_attrKind_2819_);
                            crate::leanh::lean_dec(v_attrs_x3f_2817_);
                            crate::leanh::lean_dec(v___y_2813_);
                            v___x_2979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_2979_;
                        } else {
                            v___x_2980_ = l_Lean_Elab_Command_getRef___redArg(v___y_2814_);
                            if crate::leanh::lean_obj_tag(v___x_2980_) == 0 {
                                v_a_2981_ = crate::leanh::lean_ctor_get(v___x_2980_, 0);
                                crate::leanh::lean_inc(v_a_2981_);
                                crate::leanh::lean_dec_ref_known(v___x_2980_, 1);
                                v_fileName_2982_ = crate::leanh::lean_ctor_get(v___y_2814_, 0);
                                v_fileMap_2983_ = crate::leanh::lean_ctor_get(v___y_2814_, 1);
                                v_currRecDepth_2984_ = crate::leanh::lean_ctor_get(v___y_2814_, 2);
                                v_cmdPos_2985_ = crate::leanh::lean_ctor_get(v___y_2814_, 3);
                                v_macroStack_2986_ = crate::leanh::lean_ctor_get(v___y_2814_, 4);
                                v_quotContext_x3f_2987_ =
                                    crate::leanh::lean_ctor_get(v___y_2814_, 5);
                                v_currMacroScope_2988_ =
                                    crate::leanh::lean_ctor_get(v___y_2814_, 6);
                                v_snap_x3f_2989_ = crate::leanh::lean_ctor_get(v___y_2814_, 8);
                                v_cancelTk_x3f_2990_ = crate::leanh::lean_ctor_get(v___y_2814_, 9);
                                v_suppressElabErrors_2991_ = crate::leanh::lean_ctor_get_uint8(
                                    v___y_2814_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10)
                                        as u32,
                                );
                                v___x_2992_ = l_Lean_Syntax_getArg(v___x_2976_, v___x_2729_);
                                crate::leanh::lean_dec(v___x_2976_);
                                v_alts_2993_ = l_Lean_Syntax_getArgs(v___x_2992_);
                                crate::leanh::lean_dec(v___x_2992_);
                                v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                v___x_2995_ = crate::leanh::lean_box(2);
                                crate::leanh::lean_inc_ref(v_alts_2993_);
                                v___x_2996_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_2995_);
                                crate::leanh::lean_ctor_set(v___x_2996_, 1, v___x_2994_);
                                crate::leanh::lean_ctor_set(v___x_2996_, 2, v_alts_2993_);
                                v___f_2997_ = crate::leanh::lean_alloc_closure(
                                    l_Lean_Elab_Command_elabMacroRules___lam__5___boxed
                                        as *mut core::ffi::c_void,
                                    15,
                                    10,
                                );
                                crate::leanh::lean_closure_set(v___f_2997_, 0, v___x_2977_);
                                crate::leanh::lean_closure_set(v___f_2997_, 1, v___x_2661_);
                                crate::leanh::lean_closure_set(v___f_2997_, 2, v_attrKind_2819_);
                                crate::leanh::lean_closure_set(v___f_2997_, 3, v___x_2660_);
                                crate::leanh::lean_closure_set(v___f_2997_, 4, v___x_2729_);
                                crate::leanh::lean_closure_set(v___f_2997_, 5, v_attrs_x3f_2817_);
                                crate::leanh::lean_closure_set(v___f_2997_, 6, v___x_2658_);
                                crate::leanh::lean_closure_set(v___f_2997_, 7, v___x_2659_);
                                crate::leanh::lean_closure_set(v___f_2997_, 8, v___x_2820_);
                                crate::leanh::lean_closure_set(v___f_2997_, 9, v___y_2813_);
                                v___x_2998_ = lean_mk_empty_array_with_capacity(v___x_2818_);
                                v___x_2999_ = lean_array_push(v___x_2998_, v_tk_2825_);
                                v___x_3000_ = lean_array_push(v___x_2999_, v___x_2996_);
                                v___x_3001_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3001_, 0, v___x_2995_);
                                crate::leanh::lean_ctor_set(v___x_3001_, 1, v___x_2994_);
                                crate::leanh::lean_ctor_set(v___x_3001_, 2, v___x_3000_);
                                v_ref_3002_ = l_Lean_replaceRef(v___x_3001_, v_a_2981_);
                                crate::leanh::lean_dec(v_a_2981_);
                                crate::leanh::lean_dec_ref_known(v___x_3001_, 3);
                                crate::leanh::lean_inc(v_cancelTk_x3f_2990_);
                                crate::leanh::lean_inc(v_snap_x3f_2989_);
                                crate::leanh::lean_inc(v_currMacroScope_2988_);
                                crate::leanh::lean_inc(v_quotContext_x3f_2987_);
                                crate::leanh::lean_inc(v_macroStack_2986_);
                                crate::leanh::lean_inc(v_cmdPos_2985_);
                                crate::leanh::lean_inc(v_currRecDepth_2984_);
                                crate::leanh::lean_inc_ref(v_fileMap_2983_);
                                crate::leanh::lean_inc_ref(v_fileName_2982_);
                                v___x_3003_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_3003_, 0, v_fileName_2982_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 1, v_fileMap_2983_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 2, v_currRecDepth_2984_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 3, v_cmdPos_2985_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 4, v_macroStack_2986_);
                                crate::leanh::lean_ctor_set(
                                    v___x_3003_,
                                    5,
                                    v_quotContext_x3f_2987_,
                                );
                                crate::leanh::lean_ctor_set(v___x_3003_, 6, v_currMacroScope_2988_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 7, v_ref_3002_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 8, v_snap_x3f_2989_);
                                crate::leanh::lean_ctor_set(v___x_3003_, 9, v_cancelTk_x3f_2990_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_3003_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10)
                                        as u32,
                                    v_suppressElabErrors_2991_,
                                );
                                v___x_3004_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(
                                    v_alts_2993_,
                                    v___x_2660_,
                                    v___f_2997_,
                                    v___x_3003_,
                                    v___y_2815_,
                                );
                                crate::leanh::lean_dec_ref_known(v___x_3003_, 10);
                                crate::leanh::lean_dec_ref(v_alts_2993_);
                                if crate::leanh::lean_obj_tag(v___x_3004_) == 0 {
                                    v_a_3005_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                                    v_isSharedCheck_3012_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3004_)) as u8;
                                    if v_isSharedCheck_3012_ == 0 {
                                        v___x_3007_ = v___x_3004_;
                                        v_isShared_3008_ = v_isSharedCheck_3012_;
                                        state = 11;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3005_);
                                        crate::leanh::lean_dec(v___x_3004_);
                                        v___x_3007_ = crate::leanh::lean_box(0);
                                        v_isShared_3008_ = v_isSharedCheck_3012_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    v_a_3013_ = crate::leanh::lean_ctor_get(v___x_3004_, 0);
                                    v_isSharedCheck_3020_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3004_)) as u8;
                                    if v_isSharedCheck_3020_ == 0 {
                                        v___x_3015_ = v___x_3004_;
                                        v_isShared_3016_ = v_isSharedCheck_3020_;
                                        state = 13;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3013_);
                                        crate::leanh::lean_dec(v___x_3004_);
                                        v___x_3015_ = crate::leanh::lean_box(0);
                                        v_isShared_3016_ = v_isSharedCheck_3020_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_2976_);
                                crate::leanh::lean_dec(v_tk_2825_);
                                crate::leanh::lean_dec(v_attrKind_2819_);
                                crate::leanh::lean_dec(v_attrs_x3f_2817_);
                                crate::leanh::lean_dec(v___y_2813_);
                                return v___x_2980_;
                            }
                        }
                    }
                }
            }
            9 => {
                if v_isShared_2970_ == 0 {
                    v___x_2972_ = v___x_2969_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2972_;
            }
            11 => {
                if v_isShared_3008_ == 0 {
                    v___x_3010_ = v___x_3007_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
                    v___x_3010_ = v_reuseFailAlloc_3011_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3010_;
            }
            13 => {
                if v_isShared_3016_ == 0 {
                    v___x_3018_ = v___x_3015_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
                    v___x_3018_ = v_reuseFailAlloc_3019_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3018_;
            }
            15 => {
                v___x_3025_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3026_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_3025_);
                v___x_3027_ = l_Lean_Syntax_isNone(v___x_3026_);
                if v___x_3027_ == 0 {
                    crate::leanh::lean_inc(v___x_3026_);
                    v___x_3028_ = l_Lean_Syntax_matchesNull(v___x_3026_, v___x_3025_);
                    if v___x_3028_ == 0 {
                        crate::leanh::lean_dec(v___x_3026_);
                        crate::leanh::lean_dec(v_doc_x3f_3022_);
                        crate::leanh::lean_dec(v_stx_2645_);
                        v___x_3029_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                        return v___x_3029_;
                    } else {
                        v___x_3030_ = l_Lean_Syntax_getArg(v___x_3026_, v___x_2729_);
                        crate::leanh::lean_dec(v___x_3026_);
                        v___x_3031_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15;
                        crate::leanh::lean_inc(v___x_3030_);
                        v___x_3032_ = l_Lean_Syntax_isOfKind(v___x_3030_, v___x_3031_);
                        if v___x_3032_ == 0 {
                            crate::leanh::lean_dec(v___x_3030_);
                            crate::leanh::lean_dec(v_doc_x3f_3022_);
                            crate::leanh::lean_dec(v_stx_2645_);
                            v___x_3033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_3033_;
                        } else {
                            v___x_3034_ = l_Lean_Syntax_getArg(v___x_3030_, v___x_3025_);
                            crate::leanh::lean_dec(v___x_3030_);
                            v_attrs_x3f_3035_ = l_Lean_Syntax_getArgs(v___x_3034_);
                            crate::leanh::lean_dec(v___x_3034_);
                            v___x_3036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3036_, 0, v_attrs_x3f_3035_);
                            v___y_2813_ = v_doc_x3f_3022_;
                            v___y_2814_ = v___y_3023_;
                            v___y_2815_ = v___y_3024_;
                            v___y_2816_ = v___x_3025_;
                            v_attrs_x3f_2817_ = v___x_3036_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3026_);
                    v___x_3037_ = crate::leanh::lean_box(0);
                    v___y_2813_ = v_doc_x3f_3022_;
                    v___y_2814_ = v___y_3023_;
                    v___y_2815_ = v___y_3024_;
                    v___y_2816_ = v___x_3025_;
                    v_attrs_x3f_2817_ = v___x_3037_;
                    state = 8;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__1___boxed(
    mut v_stx_3049_: *mut crate::leanh::LeanObject,
    mut v___y_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3053_ =
        l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_3049_, v___y_3050_, v___y_3051_);
    crate::leanh::lean_dec(v___y_3051_);
    crate::leanh::lean_dec_ref(v___y_3050_);
    return v_res_3053_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules(
    mut v_a_3055_: *mut crate::leanh::LeanObject,
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_a_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3059_ = l_Lean_Elab_Command_elabMacroRules___closed__0;
    v___x_3060_ = l_Lean_Elab_Command_adaptExpander(v___f_3059_, v_a_3055_, v_a_3056_, v_a_3057_);
    return v___x_3060_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___boxed(
    mut v_a_3061_: *mut crate::leanh::LeanObject,
    mut v_a_3062_: *mut crate::leanh::LeanObject,
    mut v_a_3063_: *mut crate::leanh::LeanObject,
    mut v_a_3064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3065_ = l_Lean_Elab_Command_elabMacroRules(v_a_3061_, v_a_3062_, v_a_3063_);
    crate::leanh::lean_dec(v_a_3063_);
    crate::leanh::lean_dec_ref(v_a_3062_);
    return v_res_3065_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3073_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3074_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1;
    v___x_3075_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1;
    v___x_3076_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabMacroRules___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_3077_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3073_,
        v___x_3074_,
        v___x_3075_,
        v___x_3076_,
    );
    return v___x_3077_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___boxed(
    mut v_a_3078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3079_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
    return v_res_3079_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3106_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1;
    v___x_3107_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6;
    v___x_3108_ = l_Lean_addBuiltinDeclarationRanges(v___x_3106_, v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(
    mut v_a_3109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3110_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
    return v_res_3110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_MacroRules(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AuxDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_MacroRules(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_MacroRules(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Syntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_AuxDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MacroRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_MacroRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_MacroRules(builtin);
}
