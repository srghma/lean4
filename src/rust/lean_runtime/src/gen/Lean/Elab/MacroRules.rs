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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_3, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0_value: LeanStringObject<61> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 61, m_capacity: 61, m_length: 60, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value) as *mut LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7_value) as *mut LeanObject,16529391333736644786 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__10_value) as *mut LeanObject,9855511589286918680 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__14_value) as *mut LeanObject,11985596712582660667 as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16_value: LeanStringObject<63> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 63, m_capacity: 63, m_length: 62, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 109, 97, 99, 114, 111, 95, 114, 117, 108, 101, 115, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value: LeanStringObject<11> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__3_value)
                as *mut LeanObject,
            3631122813654456582 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__8: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value)
                as *mut LeanObject,
            14665357199263665561 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__9_value) as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value: LeanStringObject<4> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value: LeanStringObject<16> =
    LeanStringObject {
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
            110, 111, 69, 114, 114, 111, 114, 73, 102, 85, 110, 117, 115, 101, 100, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value: LeanStringObject<20> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 20,
        m_capacity: 20,
        m_length: 19,
        m_data: [
            110, 111, 95, 101, 114, 114, 111, 114, 95, 105, 102, 95, 117, 110, 117, 115, 101, 100,
            37, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__16_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value)
                as *mut LeanObject,
            8214547835296698684 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__20_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__21_value)
                as *mut LeanObject,
            8171668748642392738 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__18_value)
                as *mut LeanObject,
            3883738120033471353 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__22_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__24_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__23_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value: LeanStringObject<39> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 39,
        m_capacity: 39,
        m_length: 38,
        m_data: [
            76, 101, 97, 110, 46, 77, 97, 99, 114, 111, 46, 69, 120, 99, 101, 112, 116, 105, 111,
            110, 46, 117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 83, 121, 110, 116, 97,
            120, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__25_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__26_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__26: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value)
                as *mut LeanObject,
            11510100434945111860 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
                as *mut LeanObject,
            16981400742628996529 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__31_value)
                as *mut LeanObject,
            6797826372810318163 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__33_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value: LeanStringObject<13> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__34: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__34_value)
                as *mut LeanObject,
            7499624980761693169 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__35_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__36_value)
                as *mut LeanObject,
            4584992172905639687 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__37_value)
                as *mut LeanObject,
            5370970300127562257 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRulesAux___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__39_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2_value: LeanStringObject<2> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0_value)
                as *mut LeanObject,
            127604530719969405 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__7_value)
                as *mut LeanObject,
            18105168627502861736 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__4_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__3_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value: LeanStringObject<9> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value: LeanStringObject<9> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__8_value)
                as *mut LeanObject,
            7983999284776576032 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__12_value)
                as *mut LeanObject,
            13242179749370575553 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__11_value)
                as *mut LeanObject,
            312453245906544776 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__12_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__13_value)
                as *mut LeanObject,
            5117844058249666356 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6_value) as *mut LeanObject,16572064140653406795 as *mut LeanObject] };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__0_value)
                as *mut LeanObject,
            2533412339571800130 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value)
                as *mut LeanObject,
            17342580262104060118 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value: LeanCtorObject<3> =
    LeanCtorObject {
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
                l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__16_value)
                as *mut LeanObject,
            9063780239635860524 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabMacroRules___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Command_elabMacroRules___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Command_elabMacroRules___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRules___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 77, 97, 99, 114, 111, 82, 117, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__29_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacroRulesAux___closed__30_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__0_value) as *mut LeanObject,11551791596232990586 as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,((( 38 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 68 as usize) << 1) | 1) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__0_value) as *mut LeanObject,((( 38 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__1_value) as *mut LeanObject,((( 32 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 50 as usize) << 1) | 1) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__3_value) as *mut LeanObject,((( 42 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__4_value) as *mut LeanObject,((( 56 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    v___x_1556_ = lean_box(0);
    v___x_1557_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1558_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1558_, 0, v___x_1557_);
    lean_ctor_set(v___x_1558_, 1, v___x_1556_);
    return v___x_1558_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    v___x_1560_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___closed__0);
    v___x_1561_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1561_, 0, v___x_1560_);
    return v___x_1561_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg___boxed(
    mut v___y_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1563_: *mut LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
    return v_res_1563_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(
    mut v_00_u03b1_1564_: *mut LeanObject,
    mut v___y_1565_: *mut LeanObject,
    mut v___y_1566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    v___x_1568_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
    return v___x_1568_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___boxed(
    mut v_00_u03b1_1569_: *mut LeanObject,
    mut v___y_1570_: *mut LeanObject,
    mut v___y_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1573_: *mut LeanObject = core::ptr::null_mut();
    v_res_1573_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0(
            v_00_u03b1_1569_,
            v___y_1570_,
            v___y_1571_,
        );
    lean_dec(v___y_1571_);
    lean_dec_ref(v___y_1570_);
    return v_res_1573_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(
    mut v___y_1574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1576_ = lean_st_ref_get(v___y_1574_);
    v_env_1577_ = lean_ctor_get(v___x_1576_, 0);
    lean_inc_ref(v_env_1577_);
    lean_dec(v___x_1576_);
    v___x_1578_ = l_Lean_Environment_header(v_env_1577_);
    lean_dec_ref(v_env_1577_);
    v_mainModule_1579_ = lean_ctor_get(v___x_1578_, 0);
    lean_inc(v_mainModule_1579_);
    lean_dec_ref(v___x_1578_);
    v___x_1580_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1580_, 0, v_mainModule_1579_);
    return v___x_1580_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg___boxed(
    mut v___y_1581_: *mut LeanObject,
    mut v___y_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1583_: *mut LeanObject = core::ptr::null_mut();
    v_res_1583_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(
            v___y_1581_,
        );
    lean_dec(v___y_1581_);
    return v_res_1583_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(
    mut v___y_1584_: *mut LeanObject,
    mut v___y_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    v___x_1587_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(
            v___y_1585_,
        );
    return v___x_1587_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___boxed(
    mut v___y_1588_: *mut LeanObject,
    mut v___y_1589_: *mut LeanObject,
    mut v___y_1590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1591_: *mut LeanObject = core::ptr::null_mut();
    v_res_1591_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3(
        v___y_1588_,
        v___y_1589_,
    );
    lean_dec(v___y_1589_);
    lean_dec_ref(v___y_1588_);
    return v_res_1591_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    v___x_1592_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1592_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1593_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_1594_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1594_, 0, v___x_1593_);
    return v___x_1594_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1595_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_1596_ = lean_unsigned_to_nat(0);
    v___x_1597_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1597_, 0, v___x_1596_);
    lean_ctor_set(v___x_1597_, 1, v___x_1596_);
    lean_ctor_set(v___x_1597_, 2, v___x_1596_);
    lean_ctor_set(v___x_1597_, 3, v___x_1596_);
    lean_ctor_set(v___x_1597_, 4, v___x_1595_);
    lean_ctor_set(v___x_1597_, 5, v___x_1595_);
    lean_ctor_set(v___x_1597_, 6, v___x_1595_);
    lean_ctor_set(v___x_1597_, 7, v___x_1595_);
    lean_ctor_set(v___x_1597_, 8, v___x_1595_);
    lean_ctor_set(v___x_1597_, 9, v___x_1595_);
    return v___x_1597_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut LeanObject = core::ptr::null_mut();
    v___x_1598_ = lean_unsigned_to_nat(32);
    v___x_1599_ = lean_mk_empty_array_with_capacity(v___x_1598_);
    v___x_1600_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1600_, 0, v___x_1599_);
    return v___x_1600_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_1601_: usize = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    v___x_1601_ = 5usize;
    v___x_1602_ = lean_unsigned_to_nat(0);
    v___x_1603_ = lean_unsigned_to_nat(32);
    v___x_1604_ = lean_mk_empty_array_with_capacity(v___x_1603_);
    v___x_1605_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__3);
    v___x_1606_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1606_, 0, v___x_1605_);
    lean_ctor_set(v___x_1606_, 1, v___x_1604_);
    lean_ctor_set(v___x_1606_, 2, v___x_1602_);
    lean_ctor_set(v___x_1606_, 3, v___x_1602_);
    lean_ctor_set_usize(v___x_1606_, 4, v___x_1601_);
    return v___x_1606_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1607_ = lean_box(1);
    v___x_1608_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__4);
    v___x_1609_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_1610_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1610_, 0, v___x_1609_);
    lean_ctor_set(v___x_1610_, 1, v___x_1608_);
    lean_ctor_set(v___x_1610_, 2, v___x_1607_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = lean_st_ref_get(v___y_1612_);
    v_env_1615_ = lean_ctor_get(v___x_1614_, 0);
    lean_inc_ref(v_env_1615_);
    lean_dec(v___x_1614_);
    v___x_1616_ = lean_st_ref_get(v___y_1612_);
    v_scopes_1617_ = lean_ctor_get(v___x_1616_, 2);
    lean_inc(v_scopes_1617_);
    lean_dec(v___x_1616_);
    v___x_1618_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1619_ = l_List_head_x21___redArg(v___x_1618_, v_scopes_1617_);
    lean_dec(v_scopes_1617_);
    v_opts_1620_ = lean_ctor_get(v___x_1619_, 1);
    lean_inc_ref(v_opts_1620_);
    lean_dec(v___x_1619_);
    v___x_1621_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__2);
    v___x_1622_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___closed__5);
    v___x_1623_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1623_, 0, v_env_1615_);
    lean_ctor_set(v___x_1623_, 1, v___x_1621_);
    lean_ctor_set(v___x_1623_, 2, v___x_1622_);
    lean_ctor_set(v___x_1623_, 3, v_opts_1620_);
    v___x_1624_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1624_, 0, v___x_1623_);
    lean_ctor_set(v___x_1624_, 1, v_msgData_1611_);
    v___x_1625_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1625_, 0, v___x_1624_);
    return v___x_1625_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1629_: *mut LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_1626_, v___y_1627_);
    lean_dec(v___y_1627_);
    return v_res_1629_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0()
-> *mut LeanObject {
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    v___x_1630_ = lean_box(1);
    v___x_1631_ = l_Lean_MessageData_ofFormat(v___x_1630_);
    return v___x_1631_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3()
-> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__2;
    v___x_1636_ = l_Lean_MessageData_ofFormat(v___x_1635_);
    return v___x_1636_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(
    mut v_x_1637_: *mut LeanObject,
    mut v_x_1638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1643_: u8 = 0;
    let mut v_before_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1660_: u8 = 0;
    let mut v_unused_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1662_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1638_) == 0 {
                    return v_x_1637_;
                } else {
                    v_head_1639_ = lean_ctor_get(v_x_1638_, 0);
                    v_tail_1640_ = lean_ctor_get(v_x_1638_, 1);
                    v_isSharedCheck_1662_ = (!lean_is_exclusive(v_x_1638_)) as u8;
                    if v_isSharedCheck_1662_ == 0 {
                        v___x_1642_ = v_x_1638_;
                        v_isShared_1643_ = v_isSharedCheck_1662_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1640_);
                        lean_inc(v_head_1639_);
                        lean_dec(v_x_1638_);
                        v___x_1642_ = lean_box(0);
                        v_isShared_1643_ = v_isSharedCheck_1662_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1644_ = lean_ctor_get(v_head_1639_, 0);
                v_isSharedCheck_1660_ = (!lean_is_exclusive(v_head_1639_)) as u8;
                if v_isSharedCheck_1660_ == 0 {
                    v_unused_1661_ = lean_ctor_get(v_head_1639_, 1);
                    lean_dec(v_unused_1661_);
                    v___x_1646_ = v_head_1639_;
                    v_isShared_1647_ = v_isSharedCheck_1660_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_1644_);
                    lean_dec(v_head_1639_);
                    v___x_1646_ = lean_box(0);
                    v_isShared_1647_ = v_isSharedCheck_1660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1648_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
                if v_isShared_1647_ == 0 {
                    lean_ctor_set_tag(v___x_1646_, 7);
                    lean_ctor_set(v___x_1646_, 1, v___x_1648_);
                    lean_ctor_set(v___x_1646_, 0, v_x_1637_);
                    v___x_1650_ = v___x_1646_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1659_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1659_, 0, v_x_1637_);
                    lean_ctor_set(v_reuseFailAlloc_1659_, 1, v___x_1648_);
                    v___x_1650_ = v_reuseFailAlloc_1659_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1651_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__3);
                if v_isShared_1643_ == 0 {
                    lean_ctor_set_tag(v___x_1642_, 7);
                    lean_ctor_set(v___x_1642_, 1, v___x_1651_);
                    lean_ctor_set(v___x_1642_, 0, v___x_1650_);
                    v___x_1653_ = v___x_1642_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1658_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 0, v___x_1650_);
                    lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1651_);
                    v___x_1653_ = v_reuseFailAlloc_1658_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1654_ = l_Lean_MessageData_ofSyntax(v_before_1644_);
                v___x_1655_ = l_Lean_indentD(v___x_1654_);
                v___x_1656_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1656_, 0, v___x_1653_);
                lean_ctor_set(v___x_1656_, 1, v___x_1655_);
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
    mut v_opts_1663_: *mut LeanObject,
    mut v_opt_1664_: *mut LeanObject,
) -> u8 {
    let mut v_name_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
    v_name_1665_ = lean_ctor_get(v_opt_1664_, 0);
    v_defValue_1666_ = lean_ctor_get(v_opt_1664_, 1);
    v_map_1667_ = lean_ctor_get(v_opts_1663_, 0);
    v___x_1668_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1667_,
            v_name_1665_,
        );
    if lean_obj_tag(v___x_1668_) == 0 {
        let mut v___x_1669_: u8 = 0;
        v___x_1669_ = (lean_unbox(v_defValue_1666_) as u8);
        return v___x_1669_;
    } else {
        let mut v_val_1670_: *mut LeanObject = core::ptr::null_mut();
        v_val_1670_ = lean_ctor_get(v___x_1668_, 0);
        lean_inc(v_val_1670_);
        lean_dec_ref_known(v___x_1668_, 1);
        if lean_obj_tag(v_val_1670_) == 1 {
            let mut v_v_1671_: u8 = 0;
            v_v_1671_ = lean_ctor_get_uint8(v_val_1670_, 0 as u32);
            lean_dec_ref_known(v_val_1670_, 0);
            return v_v_1671_;
        } else {
            let mut v___x_1672_: u8 = 0;
            lean_dec(v_val_1670_);
            v___x_1672_ = (lean_unbox(v_defValue_1666_) as u8);
            return v___x_1672_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7___boxed(
    mut v_opts_1673_: *mut LeanObject,
    mut v_opt_1674_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1675_: u8 = 0;
    let mut v_r_1676_: *mut LeanObject = core::ptr::null_mut();
    v_res_1675_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_1673_, v_opt_1674_);
    lean_dec_ref(v_opt_1674_);
    lean_dec_ref(v_opts_1673_);
    v_r_1676_ = lean_box((v_res_1675_) as usize);
    return v_r_1676_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v___x_1680_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__1;
    v___x_1681_ = l_Lean_MessageData_ofFormat(v___x_1680_);
    return v___x_1681_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(
    mut v_msgData_1682_: *mut LeanObject,
    mut v_macroStack_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_1690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1692_: u8 = 0;
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1699_: u8 = 0;
    let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1711_: u8 = 0;
    let mut v_unused_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1686_ = lean_st_ref_get(v___y_1684_);
                v_scopes_1687_ = lean_ctor_get(v___x_1686_, 2);
                lean_inc(v_scopes_1687_);
                lean_dec(v___x_1686_);
                v___x_1688_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1689_ = l_List_head_x21___redArg(v___x_1688_, v_scopes_1687_);
                lean_dec(v_scopes_1687_);
                v_opts_1690_ = lean_ctor_get(v___x_1689_, 1);
                lean_inc_ref(v_opts_1690_);
                lean_dec(v___x_1689_);
                v___x_1691_ = l_Lean_Elab_pp_macroStack;
                v___x_1692_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__7(v_opts_1690_, v___x_1691_);
                lean_dec_ref(v_opts_1690_);
                if v___x_1692_ == 0 {
                    lean_dec(v_macroStack_1683_);
                    v___x_1693_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1693_, 0, v_msgData_1682_);
                    return v___x_1693_;
                } else {
                    if lean_obj_tag(v_macroStack_1683_) == 0 {
                        v___x_1694_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1694_, 0, v_msgData_1682_);
                        return v___x_1694_;
                    } else {
                        v_head_1695_ = lean_ctor_get(v_macroStack_1683_, 0);
                        lean_inc(v_head_1695_);
                        v_after_1696_ = lean_ctor_get(v_head_1695_, 1);
                        v_isSharedCheck_1711_ = (!lean_is_exclusive(v_head_1695_)) as u8;
                        if v_isSharedCheck_1711_ == 0 {
                            v_unused_1712_ = lean_ctor_get(v_head_1695_, 0);
                            lean_dec(v_unused_1712_);
                            v___x_1698_ = v_head_1695_;
                            v_isShared_1699_ = v_isSharedCheck_1711_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_1696_);
                            lean_dec(v_head_1695_);
                            v___x_1698_ = lean_box(0);
                            v_isShared_1699_ = v_isSharedCheck_1711_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1700_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8___closed__0);
                if v_isShared_1699_ == 0 {
                    lean_ctor_set_tag(v___x_1698_, 7);
                    lean_ctor_set(v___x_1698_, 1, v___x_1700_);
                    lean_ctor_set(v___x_1698_, 0, v_msgData_1682_);
                    v___x_1702_ = v___x_1698_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1710_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_msgData_1682_);
                    lean_ctor_set(v_reuseFailAlloc_1710_, 1, v___x_1700_);
                    v___x_1702_ = v_reuseFailAlloc_1710_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1703_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___closed__2);
                v___x_1704_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v___x_1702_);
                lean_ctor_set(v___x_1704_, 1, v___x_1703_);
                v___x_1705_ = l_Lean_MessageData_ofSyntax(v_after_1696_);
                v___x_1706_ = l_Lean_indentD(v___x_1705_);
                v_msgData_1707_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_1707_, 0, v___x_1704_);
                lean_ctor_set(v_msgData_1707_, 1, v___x_1706_);
                v___x_1708_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4_spec__8(v_msgData_1707_, v_macroStack_1683_);
                v___x_1709_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1709_, 0, v___x_1708_);
                return v___x_1709_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg___boxed(
    mut v_msgData_1713_: *mut LeanObject,
    mut v_macroStack_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1717_: *mut LeanObject = core::ptr::null_mut();
    v_res_1717_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_1713_, v_macroStack_1714_, v___y_1715_);
    lean_dec(v___y_1715_);
    return v_res_1717_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(
    mut v_msg_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_a_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1722_ = l_Lean_Elab_Command_getRef___redArg(v___y_1719_);
                if lean_obj_tag(v___x_1722_) == 0 {
                    v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
                    lean_inc(v_a_1723_);
                    lean_dec_ref_known(v___x_1722_, 1);
                    v_macroStack_1724_ = lean_ctor_get(v___y_1719_, 4);
                    v___x_1725_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msg_1718_, v___y_1720_);
                    v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
                    lean_inc(v_a_1726_);
                    lean_dec_ref(v___x_1725_);
                    v___x_1727_ = l_Lean_Elab_getBetterRef(v_a_1723_, v_macroStack_1724_);
                    lean_dec(v_a_1723_);
                    lean_inc(v_macroStack_1724_);
                    v___x_1728_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_a_1726_, v_macroStack_1724_, v___y_1720_);
                    v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
                    v_isSharedCheck_1737_ = (!lean_is_exclusive(v___x_1728_)) as u8;
                    if v_isSharedCheck_1737_ == 0 {
                        v___x_1731_ = v___x_1728_;
                        v_isShared_1732_ = v_isSharedCheck_1737_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1729_);
                        lean_dec(v___x_1728_);
                        v___x_1731_ = lean_box(0);
                        v_isShared_1732_ = v_isSharedCheck_1737_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_1718_);
                    v_a_1738_ = lean_ctor_get(v___x_1722_, 0);
                    v_isSharedCheck_1745_ = (!lean_is_exclusive(v___x_1722_)) as u8;
                    if v_isSharedCheck_1745_ == 0 {
                        v___x_1740_ = v___x_1722_;
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1738_);
                        lean_dec(v___x_1722_);
                        v___x_1740_ = lean_box(0);
                        v_isShared_1741_ = v_isSharedCheck_1745_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1733_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1733_, 0, v___x_1727_);
                lean_ctor_set(v___x_1733_, 1, v_a_1729_);
                if v_isShared_1732_ == 0 {
                    lean_ctor_set_tag(v___x_1731_, 1);
                    lean_ctor_set(v___x_1731_, 0, v___x_1733_);
                    v___x_1735_ = v___x_1731_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1736_, 0, v___x_1733_);
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
                    v_reuseFailAlloc_1744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
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
    mut v_msg_1746_: *mut LeanObject,
    mut v___y_1747_: *mut LeanObject,
    mut v___y_1748_: *mut LeanObject,
    mut v___y_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_1746_, v___y_1747_, v___y_1748_);
    lean_dec(v___y_1748_);
    lean_dec_ref(v___y_1747_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(
    mut v_ref_1751_: *mut LeanObject,
    mut v_msg_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_1765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1767_: u8 = 0;
    let mut v_ref_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1756_ = l_Lean_Elab_Command_getRef___redArg(v___y_1753_);
                if lean_obj_tag(v___x_1756_) == 0 {
                    v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
                    lean_inc(v_a_1757_);
                    lean_dec_ref_known(v___x_1756_, 1);
                    v_fileName_1758_ = lean_ctor_get(v___y_1753_, 0);
                    v_fileMap_1759_ = lean_ctor_get(v___y_1753_, 1);
                    v_currRecDepth_1760_ = lean_ctor_get(v___y_1753_, 2);
                    v_cmdPos_1761_ = lean_ctor_get(v___y_1753_, 3);
                    v_macroStack_1762_ = lean_ctor_get(v___y_1753_, 4);
                    v_quotContext_x3f_1763_ = lean_ctor_get(v___y_1753_, 5);
                    v_currMacroScope_1764_ = lean_ctor_get(v___y_1753_, 6);
                    v_snap_x3f_1765_ = lean_ctor_get(v___y_1753_, 8);
                    v_cancelTk_x3f_1766_ = lean_ctor_get(v___y_1753_, 9);
                    v_suppressElabErrors_1767_ = lean_ctor_get_uint8(
                        v___y_1753_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_1768_ = l_Lean_replaceRef(v_ref_1751_, v_a_1757_);
                    lean_dec(v_a_1757_);
                    lean_inc(v_cancelTk_x3f_1766_);
                    lean_inc(v_snap_x3f_1765_);
                    lean_inc(v_currMacroScope_1764_);
                    lean_inc(v_quotContext_x3f_1763_);
                    lean_inc(v_macroStack_1762_);
                    lean_inc(v_cmdPos_1761_);
                    lean_inc(v_currRecDepth_1760_);
                    lean_inc_ref(v_fileMap_1759_);
                    lean_inc_ref(v_fileName_1758_);
                    v___x_1769_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_1769_, 0, v_fileName_1758_);
                    lean_ctor_set(v___x_1769_, 1, v_fileMap_1759_);
                    lean_ctor_set(v___x_1769_, 2, v_currRecDepth_1760_);
                    lean_ctor_set(v___x_1769_, 3, v_cmdPos_1761_);
                    lean_ctor_set(v___x_1769_, 4, v_macroStack_1762_);
                    lean_ctor_set(v___x_1769_, 5, v_quotContext_x3f_1763_);
                    lean_ctor_set(v___x_1769_, 6, v_currMacroScope_1764_);
                    lean_ctor_set(v___x_1769_, 7, v_ref_1768_);
                    lean_ctor_set(v___x_1769_, 8, v_snap_x3f_1765_);
                    lean_ctor_set(v___x_1769_, 9, v_cancelTk_x3f_1766_);
                    lean_ctor_set_uint8(
                        v___x_1769_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_1767_,
                    );
                    v___x_1770_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_1752_, v___x_1769_, v___y_1754_);
                    lean_dec_ref_known(v___x_1769_, 10);
                    return v___x_1770_;
                } else {
                    lean_dec_ref(v_msg_1752_);
                    v_a_1771_ = lean_ctor_get(v___x_1756_, 0);
                    v_isSharedCheck_1778_ = (!lean_is_exclusive(v___x_1756_)) as u8;
                    if v_isSharedCheck_1778_ == 0 {
                        v___x_1773_ = v___x_1756_;
                        v_isShared_1774_ = v_isSharedCheck_1778_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1771_);
                        lean_dec(v___x_1756_);
                        v___x_1773_ = lean_box(0);
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
                    v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
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
    mut v_ref_1779_: *mut LeanObject,
    mut v_msg_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1784_: *mut LeanObject = core::ptr::null_mut();
    v_res_1784_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(
        v_ref_1779_,
        v_msg_1780_,
        v___y_1781_,
        v___y_1782_,
    );
    lean_dec(v___y_1782_);
    lean_dec_ref(v___y_1781_);
    lean_dec(v_ref_1779_);
    return v_res_1784_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(
    mut v_k_1788_: *mut LeanObject,
    mut v_as_1789_: *mut LeanObject,
    mut v_sz_1790_: usize,
    mut v_i_1791_: usize,
    mut v_b_1792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1793_: u8 = 0;
    let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: usize = 0;
    let mut v___x_1800_: usize = 0;
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1793_ = lean_usize_dec_lt(v_i_1791_, v_sz_1790_);
                if v___x_1793_ == 0 {
                    lean_dec(v_k_1788_);
                    lean_inc_ref(v_b_1792_);
                    return v_b_1792_;
                } else {
                    v___x_1794_ = lean_box(0);
                    v_a_1795_ = lean_array_uget_borrowed(v_as_1789_, v_i_1791_);
                    lean_inc(v_a_1795_);
                    v___x_1796_ = l_Lean_Syntax_getKind(v_a_1795_);
                    lean_inc(v_k_1788_);
                    v___x_1797_ = l_Lean_Elab_Command_checkRuleKind(v___x_1796_, v_k_1788_);
                    lean_dec(v___x_1796_);
                    if v___x_1797_ == 0 {
                        v___x_1798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0;
                        v___x_1799_ = 1usize;
                        v___x_1800_ = lean_usize_add(v_i_1791_, v___x_1799_);
                        v_i_1791_ = v___x_1800_;
                        v_b_1792_ = v___x_1798_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_k_1788_);
                        lean_inc(v_a_1795_);
                        v___x_1802_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1802_, 0, v_a_1795_);
                        v___x_1803_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1803_, 0, v___x_1802_);
                        v___x_1804_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1804_, 0, v___x_1803_);
                        lean_ctor_set(v___x_1804_, 1, v___x_1794_);
                        return v___x_1804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___boxed(
    mut v_k_1805_: *mut LeanObject,
    mut v_as_1806_: *mut LeanObject,
    mut v_sz_1807_: *mut LeanObject,
    mut v_i_1808_: *mut LeanObject,
    mut v_b_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1810_: usize = 0;
    let mut v_i_boxed_1811_: usize = 0;
    let mut v_res_1812_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1810_ = lean_unbox_usize(v_sz_1807_);
    lean_dec(v_sz_1807_);
    v_i_boxed_1811_ = lean_unbox_usize(v_i_1808_);
    lean_dec(v_i_1808_);
    v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_1805_, v_as_1806_, v_sz_boxed_1810_, v_i_boxed_1811_, v_b_1809_);
    lean_dec_ref(v_b_1809_);
    lean_dec_ref(v_as_1806_);
    return v_res_1812_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__0;
    v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__2;
    v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12()
-> *mut LeanObject {
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v___x_1832_ = l_Array_mkArray0(lean_box(0));
    return v___x_1832_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17()
-> *mut LeanObject {
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    v___x_1838_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__16;
    v___x_1839_ = l_Lean_stringToMessageData(v___x_1838_);
    return v___x_1839_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(
    mut v_k_1840_: *mut LeanObject,
    mut v_sz_1841_: usize,
    mut v_i_1842_: usize,
    mut v_bs_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1847_: u8 = 0;
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: usize = 0;
    let mut v___x_1855_: usize = 0;
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1864_: u8 = 0;
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1868_: u8 = 0;
    let mut v___y_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: u8 = 0;
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: u8 = 0;
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pat_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quoted_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: u8 = 0;
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_1920_: usize = 0;
    let mut v___x_1921_: usize = 0;
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pat_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pats_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1937_: u8 = 0;
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1941_: u8 = 0;
    let mut v_a_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1945_: u8 = 0;
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1949_: u8 = 0;
    let mut v_a_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1953_: u8 = 0;
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1957_: u8 = 0;
    let mut v___x_1958_: u8 = 0;
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1963_: u8 = 0;
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1847_ = lean_usize_dec_lt(v_i_1842_, v_sz_1841_);
                if v___x_1847_ == 0 {
                    lean_dec(v_k_1840_);
                    v___x_1848_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1848_, 0, v_bs_1843_);
                    return v___x_1848_;
                } else {
                    v_v_1849_ = lean_array_uget(v_bs_1843_, v_i_1842_);
                    v___x_1850_ = lean_unsigned_to_nat(0);
                    v_bs_x27_1851_ = lean_array_uset(v_bs_1843_, v_i_1842_, v___x_1850_);
                    v___x_1878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__8;
                    lean_inc(v_v_1849_);
                    v___x_1879_ = l_Lean_Syntax_isOfKind(v_v_1849_, v___x_1878_);
                    if v___x_1879_ == 0 {
                        lean_dec(v_v_1849_);
                        v___x_1880_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                        v___y_1859_ = v___x_1880_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1881_ = lean_unsigned_to_nat(1);
                        v___x_1882_ = l_Lean_Syntax_getArg(v_v_1849_, v___x_1881_);
                        lean_inc(v___x_1882_);
                        v___x_1883_ = l_Lean_Syntax_matchesNull(v___x_1882_, v___x_1881_);
                        if v___x_1883_ == 0 {
                            lean_dec(v___x_1882_);
                            lean_dec(v_v_1849_);
                            v___x_1884_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            v___y_1859_ = v___x_1884_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1885_ = l_Lean_Syntax_getArg(v___x_1882_, v___x_1850_);
                            lean_dec(v___x_1882_);
                            v___x_1886_ = lean_unsigned_to_nat(3);
                            v___x_1887_ = l_Lean_Syntax_getArg(v_v_1849_, v___x_1886_);
                            v___x_1901_ = l_Lean_Syntax_getArgs(v___x_1885_);
                            lean_dec(v___x_1885_);
                            v___x_1902_ = lean_box(0);
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
                                    if lean_obj_tag(v___x_1959_) == 0 {
                                        lean_dec_ref_known(v___x_1959_, 1);
                                        v___y_1905_ = v___y_1844_;
                                        v___y_1906_ = v___y_1845_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_dec(v_pat_1903_);
                                        lean_dec_ref(v___x_1901_);
                                        lean_dec(v___x_1887_);
                                        lean_dec_ref(v_bs_x27_1851_);
                                        lean_dec(v_v_1849_);
                                        lean_dec(v_k_1840_);
                                        v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
                                        v_isSharedCheck_1967_ =
                                            (!lean_is_exclusive(v___x_1959_)) as u8;
                                        if v_isSharedCheck_1967_ == 0 {
                                            v___x_1962_ = v___x_1959_;
                                            v_isShared_1963_ = v_isSharedCheck_1967_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1960_);
                                            lean_dec(v___x_1959_);
                                            v___x_1962_ = lean_box(0);
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
                if lean_obj_tag(v___y_1859_) == 0 {
                    v_a_1860_ = lean_ctor_get(v___y_1859_, 0);
                    lean_inc(v_a_1860_);
                    lean_dec_ref_known(v___y_1859_, 1);
                    v_a_1853_ = v_a_1860_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref(v_bs_x27_1851_);
                    lean_dec(v_k_1840_);
                    v_a_1861_ = lean_ctor_get(v___y_1859_, 0);
                    v_isSharedCheck_1868_ = (!lean_is_exclusive(v___y_1859_)) as u8;
                    if v_isSharedCheck_1868_ == 0 {
                        v___x_1863_ = v___y_1859_;
                        v_isShared_1864_ = v_isSharedCheck_1868_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1861_);
                        lean_dec(v___y_1859_);
                        v___x_1863_ = lean_box(0);
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
                    v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
                    v___x_1866_ = v_reuseFailAlloc_1867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1866_;
            }
            5 => {
                v___x_1872_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__1);
                lean_inc(v_k_1840_);
                v___x_1873_ = l_Lean_MessageData_ofName(v_k_1840_);
                v___x_1874_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1874_, 0, v___x_1872_);
                lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
                v___x_1876_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1876_, 0, v___x_1874_);
                lean_ctor_set(v___x_1876_, 1, v___x_1875_);
                v___x_1877_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_1849_, v___x_1876_, v___y_1870_, v___y_1871_);
                lean_dec(v_v_1849_);
                v___y_1859_ = v___x_1877_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9;
                lean_inc_n(v___y_1890_, 4);
                v___x_1892_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1892_, 0, v___y_1890_);
                lean_ctor_set(v___x_1892_, 1, v___x_1891_);
                v___x_1893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                v___x_1894_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                v___x_1895_ = l_Array_append___redArg(v___x_1894_, v___y_1889_);
                lean_dec_ref(v___y_1889_);
                v___x_1896_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_1896_, 0, v___y_1890_);
                lean_ctor_set(v___x_1896_, 1, v___x_1893_);
                lean_ctor_set(v___x_1896_, 2, v___x_1895_);
                v___x_1897_ = l_Lean_Syntax_node1(v___y_1890_, v___x_1893_, v___x_1896_);
                v___x_1898_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13;
                v___x_1899_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_1899_, 0, v___y_1890_);
                lean_ctor_set(v___x_1899_, 1, v___x_1898_);
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
                lean_inc(v_pat_1903_);
                v_quoted_1907_ = l_Lean_Syntax_getQuotContent(v_pat_1903_);
                lean_inc(v_quoted_1907_);
                v_k_x27_1908_ = l_Lean_Syntax_getKind(v_quoted_1907_);
                lean_inc(v_k_1840_);
                v___x_1909_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_1908_, v_k_1840_);
                if v___x_1909_ == 0 {
                    v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__15;
                    v___x_1911_ = lean_name_eq(v_k_x27_1908_, v___x_1910_);
                    if v___x_1911_ == 0 {
                        lean_dec(v_quoted_1907_);
                        lean_dec(v_pat_1903_);
                        lean_dec_ref(v___x_1901_);
                        lean_dec(v___x_1887_);
                        v___x_1912_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__17);
                        v___x_1913_ = l_Lean_MessageData_ofName(v_k_x27_1908_);
                        v___x_1914_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1914_, 0, v___x_1912_);
                        lean_ctor_set(v___x_1914_, 1, v___x_1913_);
                        v___x_1915_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__3);
                        v___x_1916_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_1916_, 0, v___x_1914_);
                        lean_ctor_set(v___x_1916_, 1, v___x_1915_);
                        v___x_1917_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(v_v_1849_, v___x_1916_, v___y_1905_, v___y_1906_);
                        lean_dec(v_v_1849_);
                        v___y_1859_ = v___x_1917_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v_k_x27_1908_);
                        v___x_1918_ = l_Lean_Syntax_getArgs(v_quoted_1907_);
                        lean_dec(v_quoted_1907_);
                        v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2___closed__0;
                        v_sz_1920_ = lean_array_size(v___x_1918_);
                        v___x_1921_ = 0usize;
                        lean_inc(v_k_1840_);
                        v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabMacroRulesAux_spec__2(v_k_1840_, v___x_1918_, v_sz_1920_, v___x_1921_, v___x_1919_);
                        lean_dec_ref(v___x_1918_);
                        v_fst_1923_ = lean_ctor_get(v___x_1922_, 0);
                        lean_inc(v_fst_1923_);
                        lean_dec_ref(v___x_1922_);
                        if lean_obj_tag(v_fst_1923_) == 0 {
                            lean_dec(v_pat_1903_);
                            lean_dec_ref(v___x_1901_);
                            lean_dec(v___x_1887_);
                            v___y_1870_ = v___y_1905_;
                            v___y_1871_ = v___y_1906_;
                            state = 5;
                            continue;
                        } else {
                            v_val_1924_ = lean_ctor_get(v_fst_1923_, 0);
                            lean_inc(v_val_1924_);
                            lean_dec_ref_known(v_fst_1923_, 1);
                            if lean_obj_tag(v_val_1924_) == 0 {
                                lean_dec(v_pat_1903_);
                                lean_dec_ref(v___x_1901_);
                                lean_dec(v___x_1887_);
                                v___y_1870_ = v___y_1905_;
                                v___y_1871_ = v___y_1906_;
                                state = 5;
                                continue;
                            } else {
                                lean_dec(v_v_1849_);
                                v_val_1925_ = lean_ctor_get(v_val_1924_, 0);
                                lean_inc(v_val_1925_);
                                lean_dec_ref_known(v_val_1924_, 1);
                                v___x_1926_ = l_Lean_Elab_Command_getRef___redArg(v___y_1905_);
                                if lean_obj_tag(v___x_1926_) == 0 {
                                    v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
                                    lean_inc(v_a_1927_);
                                    lean_dec_ref_known(v___x_1926_, 1);
                                    v___x_1928_ =
                                        l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_1905_);
                                    if lean_obj_tag(v___x_1928_) == 0 {
                                        lean_dec_ref_known(v___x_1928_, 1);
                                        v_quotContext_x3f_1929_ = lean_ctor_get(v___y_1905_, 5);
                                        v_pat_1930_ = l_Lean_Syntax_setArg(
                                            v_pat_1903_,
                                            v___x_1881_,
                                            v_val_1925_,
                                        );
                                        v_pats_1931_ =
                                            lean_array_set(v___x_1901_, v___x_1850_, v_pat_1930_);
                                        v___x_1932_ =
                                            l_Lean_SourceInfo_fromRef(v_a_1927_, v___x_1909_);
                                        lean_dec(v_a_1927_);
                                        if lean_obj_tag(v_quotContext_x3f_1929_) == 0 {
                                            v___x_1933_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_1906_);
                                            if lean_obj_tag(v___x_1933_) == 0 {
                                                lean_dec_ref_known(v___x_1933_, 1);
                                                v___y_1889_ = v_pats_1931_;
                                                v___y_1890_ = v___x_1932_;
                                                state = 6;
                                                continue;
                                            } else {
                                                lean_dec(v___x_1932_);
                                                lean_dec_ref(v_pats_1931_);
                                                lean_dec(v___x_1887_);
                                                lean_dec_ref(v_bs_x27_1851_);
                                                lean_dec(v_k_1840_);
                                                v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
                                                v_isSharedCheck_1941_ =
                                                    (!lean_is_exclusive(v___x_1933_)) as u8;
                                                if v_isSharedCheck_1941_ == 0 {
                                                    v___x_1936_ = v___x_1933_;
                                                    v_isShared_1937_ = v_isSharedCheck_1941_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_1934_);
                                                    lean_dec(v___x_1933_);
                                                    v___x_1936_ = lean_box(0);
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
                                        lean_dec(v_a_1927_);
                                        lean_dec(v_val_1925_);
                                        lean_dec(v_pat_1903_);
                                        lean_dec_ref(v___x_1901_);
                                        lean_dec(v___x_1887_);
                                        lean_dec_ref(v_bs_x27_1851_);
                                        lean_dec(v_k_1840_);
                                        v_a_1942_ = lean_ctor_get(v___x_1928_, 0);
                                        v_isSharedCheck_1949_ =
                                            (!lean_is_exclusive(v___x_1928_)) as u8;
                                        if v_isSharedCheck_1949_ == 0 {
                                            v___x_1944_ = v___x_1928_;
                                            v_isShared_1945_ = v_isSharedCheck_1949_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_a_1942_);
                                            lean_dec(v___x_1928_);
                                            v___x_1944_ = lean_box(0);
                                            v_isShared_1945_ = v_isSharedCheck_1949_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_val_1925_);
                                    lean_dec(v_pat_1903_);
                                    lean_dec_ref(v___x_1901_);
                                    lean_dec(v___x_1887_);
                                    lean_dec_ref(v_bs_x27_1851_);
                                    lean_dec(v_k_1840_);
                                    v_a_1950_ = lean_ctor_get(v___x_1926_, 0);
                                    v_isSharedCheck_1957_ = (!lean_is_exclusive(v___x_1926_)) as u8;
                                    if v_isSharedCheck_1957_ == 0 {
                                        v___x_1952_ = v___x_1926_;
                                        v_isShared_1953_ = v_isSharedCheck_1957_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1950_);
                                        lean_dec(v___x_1926_);
                                        v___x_1952_ = lean_box(0);
                                        v_isShared_1953_ = v_isSharedCheck_1957_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    lean_dec(v_k_x27_1908_);
                    lean_dec(v_quoted_1907_);
                    lean_dec(v_pat_1903_);
                    lean_dec_ref(v___x_1901_);
                    lean_dec(v___x_1887_);
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
                    v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
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
                    v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
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
                    v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1956_, 0, v_a_1950_);
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
                    v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
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
    mut v_k_1968_: *mut LeanObject,
    mut v_sz_1969_: *mut LeanObject,
    mut v_i_1970_: *mut LeanObject,
    mut v_bs_1971_: *mut LeanObject,
    mut v___y_1972_: *mut LeanObject,
    mut v___y_1973_: *mut LeanObject,
    mut v___y_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_1975_: usize = 0;
    let mut v_i_boxed_1976_: usize = 0;
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_1975_ = lean_unbox_usize(v_sz_1969_);
    lean_dec(v_sz_1969_);
    v_i_boxed_1976_ = lean_unbox_usize(v_i_1970_);
    lean_dec(v_i_1970_);
    v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_1968_, v_sz_boxed_1975_, v_i_boxed_1976_, v_bs_1971_, v___y_1972_, v___y_1973_);
    lean_dec(v___y_1973_);
    lean_dec_ref(v___y_1972_);
    return v_res_1977_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4() -> *mut LeanObject {
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    v___x_1982_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__3;
    v___x_1983_ = l_String_toRawSubstring_x27(v___x_1982_);
    return v___x_1983_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8() -> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
    v___x_1989_ = l_String_toRawSubstring_x27(v___x_1988_);
    return v___x_1989_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19() -> *mut LeanObject {
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    v___x_2001_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__18;
    v___x_2002_ = l_String_toRawSubstring_x27(v___x_2001_);
    return v___x_2002_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__26() -> *mut LeanObject {
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2016_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__25;
    v___x_2017_ = l_String_toRawSubstring_x27(v___x_2016_);
    return v___x_2017_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRulesAux(
    mut v_doc_x3f_2044_: *mut LeanObject,
    mut v_attrs_x3f_2045_: *mut LeanObject,
    mut v_attrKind_2046_: *mut LeanObject,
    mut v_tk_2047_: *mut LeanObject,
    mut v_k_2048_: *mut LeanObject,
    mut v_alts_2049_: *mut LeanObject,
    mut v_a_2050_: *mut LeanObject,
    mut v_a_2051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2053_: usize = 0;
    let mut v___x_2054_: usize = 0;
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___y_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: u8 = 0;
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: u8 = 0;
    let mut v___y_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2205_: u8 = 0;
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2209_: u8 = 0;
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2233_: u8 = 0;
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut v_isSharedCheck_2238_: u8 = 0;
    let mut v_a_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2246_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2053_ = lean_array_size(v_alts_2049_);
                v___x_2054_ = 0usize;
                lean_inc(v_k_2048_);
                v___x_2055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4(v_k_2048_, v_sz_2053_, v___x_2054_, v_alts_2049_, v_a_2050_, v_a_2051_);
                if lean_obj_tag(v___x_2055_) == 0 {
                    v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2238_ = (!lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2238_ == 0 {
                        v___x_2058_ = v___x_2055_;
                        v_isShared_2059_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2056_);
                        lean_dec(v___x_2055_);
                        v___x_2058_ = lean_box(0);
                        v_isShared_2059_ = v_isSharedCheck_2238_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_k_2048_);
                    lean_dec(v_attrKind_2046_);
                    lean_dec(v_doc_x3f_2044_);
                    v_a_2239_ = lean_ctor_get(v___x_2055_, 0);
                    v_isSharedCheck_2246_ = (!lean_is_exclusive(v___x_2055_)) as u8;
                    if v_isSharedCheck_2246_ == 0 {
                        v___x_2241_ = v___x_2055_;
                        v_isShared_2242_ = v_isSharedCheck_2246_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2239_);
                        lean_dec(v___x_2055_);
                        v___x_2241_ = lean_box(0);
                        v_isShared_2242_ = v_isSharedCheck_2246_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2186_ = l_Lean_Elab_Command_getRef___redArg(v_a_2050_);
                if lean_obj_tag(v___x_2186_) == 0 {
                    v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
                    lean_inc(v_a_2187_);
                    lean_dec_ref_known(v___x_2186_, 1);
                    v___x_2188_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_2050_);
                    if lean_obj_tag(v___x_2188_) == 0 {
                        lean_dec_ref_known(v___x_2188_, 1);
                        v_quotContext_x3f_2189_ = lean_ctor_get(v_a_2050_, 5);
                        v___x_2190_ = 0;
                        v___x_2210_ = l_Lean_SourceInfo_fromRef(v_a_2187_, v___x_2190_);
                        lean_dec(v_a_2187_);
                        if lean_obj_tag(v_quotContext_x3f_2189_) == 0 {
                            v___x_2229_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_2051_);
                            lean_dec_ref(v___x_2229_);
                            state = 8;
                            continue;
                        } else {
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2187_);
                        lean_del_object(v___x_2058_);
                        lean_dec(v_a_2056_);
                        lean_dec(v_k_2048_);
                        lean_dec(v_attrKind_2046_);
                        lean_dec(v_doc_x3f_2044_);
                        v_a_2230_ = lean_ctor_get(v___x_2188_, 0);
                        v_isSharedCheck_2237_ = (!lean_is_exclusive(v___x_2188_)) as u8;
                        if v_isSharedCheck_2237_ == 0 {
                            v___x_2232_ = v___x_2188_;
                            v_isShared_2233_ = v_isSharedCheck_2237_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2230_);
                            lean_dec(v___x_2188_);
                            v___x_2232_ = lean_box(0);
                            v_isShared_2233_ = v_isSharedCheck_2237_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2058_);
                    lean_dec(v_a_2056_);
                    lean_dec(v_k_2048_);
                    lean_dec(v_attrKind_2046_);
                    lean_dec(v_doc_x3f_2044_);
                    return v___x_2186_;
                }
            }
            2 => {
                lean_inc_ref_n(v___y_2067_, 3);
                v___x_2072_ = l_Array_append___redArg(v___y_2067_, v___y_2071_);
                lean_dec_ref(v___y_2071_);
                lean_inc_n(v___y_2068_, 8);
                lean_inc_n(v___y_2069_, 29);
                v___x_2073_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2073_, 0, v___y_2069_);
                lean_ctor_set(v___x_2073_, 1, v___y_2068_);
                lean_ctor_set(v___x_2073_, 2, v___x_2072_);
                v___x_2074_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5;
                v___x_2075_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6;
                v___x_2076_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__0;
                lean_inc_ref_n(v___y_2066_, 9);
                v___x_2077_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2076_);
                v___x_2078_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
                v___x_2079_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2079_, 0, v___y_2069_);
                lean_ctor_set(v___x_2079_, 1, v___x_2078_);
                v___x_2080_ = l_Array_append___redArg(v___y_2067_, v___y_2063_);
                lean_dec_ref(v___y_2063_);
                v___x_2081_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2081_, 0, v___y_2069_);
                lean_ctor_set(v___x_2081_, 1, v___y_2068_);
                lean_ctor_set(v___x_2081_, 2, v___x_2080_);
                v___x_2082_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
                v___x_2083_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2083_, 0, v___y_2069_);
                lean_ctor_set(v___x_2083_, 1, v___x_2082_);
                v___x_2084_ = l_Lean_Syntax_node3(
                    v___y_2069_,
                    v___x_2077_,
                    v___x_2079_,
                    v___x_2081_,
                    v___x_2083_,
                );
                v___x_2085_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2084_);
                lean_inc_ref(v___y_2062_);
                v___x_2086_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2086_, 0, v___y_2069_);
                lean_ctor_set(v___x_2086_, 1, v___y_2062_);
                v___x_2087_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__4_once),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__4,
                );
                v___x_2088_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__5;
                lean_inc_n(v___y_2065_, 3);
                lean_inc_n(v___y_2061_, 3);
                v___x_2089_ = l_Lean_addMacroScope(v___y_2061_, v___x_2088_, v___y_2065_);
                v___x_2090_ = lean_box(0);
                v___x_2091_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2091_, 0, v___y_2069_);
                lean_ctor_set(v___x_2091_, 1, v___x_2087_);
                lean_ctor_set(v___x_2091_, 2, v___x_2089_);
                lean_ctor_set(v___x_2091_, 3, v___x_2090_);
                v___x_2092_ = 1;
                v___x_2093_ = l_Lean_mkIdentFrom(v_tk_2047_, v_k_2048_, v___x_2092_);
                v___x_2094_ =
                    l_Lean_Syntax_node2(v___y_2069_, v___y_2068_, v___x_2091_, v___x_2093_);
                v___x_2095_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
                v___x_2096_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2096_, 0, v___y_2069_);
                lean_ctor_set(v___x_2096_, 1, v___x_2095_);
                v___x_2097_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__7;
                v___x_2098_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8,
                );
                v___x_2099_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
                v___x_2100_ = l_Lean_addMacroScope(v___y_2061_, v___x_2099_, v___y_2065_);
                v___x_2101_ = l_Lean_Name_mkStr2(v___y_2066_, v___x_2097_);
                lean_inc(v___x_2101_);
                v___x_2102_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2102_, 0, v___x_2101_);
                lean_ctor_set(v___x_2102_, 1, v___x_2090_);
                v___x_2103_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2103_, 0, v___x_2101_);
                v___x_2104_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2104_, 0, v___x_2103_);
                lean_ctor_set(v___x_2104_, 1, v___x_2090_);
                v___x_2105_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2105_, 0, v___x_2102_);
                lean_ctor_set(v___x_2105_, 1, v___x_2104_);
                v___x_2106_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2106_, 0, v___y_2069_);
                lean_ctor_set(v___x_2106_, 1, v___x_2098_);
                lean_ctor_set(v___x_2106_, 2, v___x_2100_);
                lean_ctor_set(v___x_2106_, 3, v___x_2105_);
                v___x_2107_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
                v___x_2108_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2108_, 0, v___y_2069_);
                lean_ctor_set(v___x_2108_, 1, v___x_2107_);
                v___x_2109_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
                v___x_2110_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2109_);
                v___x_2111_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2111_, 0, v___y_2069_);
                lean_ctor_set(v___x_2111_, 1, v___x_2109_);
                v___x_2112_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__12;
                v___x_2113_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2112_);
                v___x_2114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__7;
                v___x_2115_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2114_);
                v___x_2116_ = l_Array_append___redArg(v___y_2067_, v_a_2056_);
                lean_dec(v_a_2056_);
                v___x_2117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__9;
                v___x_2118_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2118_, 0, v___y_2069_);
                lean_ctor_set(v___x_2118_, 1, v___x_2117_);
                v___x_2119_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__13;
                v___x_2120_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2119_);
                v___x_2121_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__14;
                v___x_2122_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2122_, 0, v___y_2069_);
                lean_ctor_set(v___x_2122_, 1, v___x_2121_);
                v___x_2123_ = l_Lean_Syntax_node1(v___y_2069_, v___x_2120_, v___x_2122_);
                v___x_2124_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2123_);
                v___x_2125_ = l_Lean_Syntax_node1(v___y_2069_, v___y_2068_, v___x_2124_);
                v___x_2126_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13;
                v___x_2127_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2127_, 0, v___y_2069_);
                lean_ctor_set(v___x_2127_, 1, v___x_2126_);
                v___x_2128_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__15;
                v___x_2129_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2128_);
                v___x_2130_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__16;
                v___x_2131_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2131_, 0, v___y_2069_);
                lean_ctor_set(v___x_2131_, 1, v___x_2130_);
                v___x_2132_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__17;
                v___x_2133_ =
                    l_Lean_Name_mkStr4(v___y_2066_, v___x_2074_, v___x_2075_, v___x_2132_);
                v___x_2134_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__19),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_elabMacroRulesAux___closed__19_once
                    ),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__19,
                );
                v___x_2135_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__20;
                v___x_2136_ = l_Lean_addMacroScope(v___y_2061_, v___x_2135_, v___y_2065_);
                v___x_2137_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__24;
                v___x_2138_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2138_, 0, v___y_2069_);
                lean_ctor_set(v___x_2138_, 1, v___x_2134_);
                lean_ctor_set(v___x_2138_, 2, v___x_2136_);
                lean_ctor_set(v___x_2138_, 3, v___x_2137_);
                v___x_2139_ = lean_obj_once(
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
                lean_inc_n(v___x_2142_, 2);
                v___x_2143_ = l_Lean_addMacroScope(v___y_2061_, v___x_2142_, v___y_2065_);
                v___x_2144_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2144_, 0, v___x_2142_);
                lean_ctor_set(v___x_2144_, 1, v___x_2090_);
                v___x_2145_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2145_, 0, v___x_2142_);
                v___x_2146_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2146_, 0, v___x_2145_);
                lean_ctor_set(v___x_2146_, 1, v___x_2090_);
                v___x_2147_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_2147_, 0, v___x_2144_);
                lean_ctor_set(v___x_2147_, 1, v___x_2146_);
                v___x_2148_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2148_, 0, v___y_2069_);
                lean_ctor_set(v___x_2148_, 1, v___x_2139_);
                lean_ctor_set(v___x_2148_, 2, v___x_2143_);
                lean_ctor_set(v___x_2148_, 3, v___x_2147_);
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
                v___x_2154_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2154_, 0, v___y_2069_);
                lean_ctor_set(v___x_2154_, 1, v___y_2068_);
                lean_ctor_set(v___x_2154_, 2, v___x_2153_);
                v___x_2155_ = l_Lean_Syntax_node1(v___y_2069_, v___x_2113_, v___x_2154_);
                v___x_2156_ =
                    l_Lean_Syntax_node2(v___y_2069_, v___x_2110_, v___x_2111_, v___x_2155_);
                v___x_2157_ = lean_unsigned_to_nat(9);
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
                lean_inc(v___y_2070_);
                v___x_2168_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2168_, 0, v___y_2069_);
                lean_ctor_set(v___x_2168_, 1, v___y_2070_);
                lean_ctor_set(v___x_2168_, 2, v___x_2167_);
                if v_isShared_2059_ == 0 {
                    lean_ctor_set(v___x_2058_, 0, v___x_2168_);
                    v___x_2170_ = v___x_2058_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2168_);
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
                v___x_2182_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                if lean_obj_tag(v_doc_x3f_2044_) == 1 {
                    v_val_2183_ = lean_ctor_get(v_doc_x3f_2044_, 0);
                    lean_inc(v_val_2183_);
                    lean_dec_ref_known(v_doc_x3f_2044_, 1);
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
                    lean_dec(v_doc_x3f_2044_);
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
                if lean_obj_tag(v___x_2193_) == 0 {
                    v_a_2194_ = lean_ctor_get(v___x_2193_, 0);
                    lean_inc(v_a_2194_);
                    lean_dec_ref_known(v___x_2193_, 1);
                    v___x_2195_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v_a_2050_);
                    if lean_obj_tag(v___x_2195_) == 0 {
                        v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
                        lean_inc(v_a_2196_);
                        lean_dec_ref_known(v___x_2195_, 1);
                        v___x_2197_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_2046_);
                        v___x_2198_ = l_Lean_SourceInfo_fromRef(v_a_2194_, v___x_2190_);
                        lean_dec(v_a_2194_);
                        if lean_obj_tag(v_quotContext_x3f_2189_) == 0 {
                            v___x_2199_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v_a_2051_);
                            v_a_2200_ = lean_ctor_get(v___x_2199_, 0);
                            lean_inc(v_a_2200_);
                            lean_dec_ref(v___x_2199_);
                            v___y_2173_ = v___y_2192_;
                            v___y_2174_ = v___x_2197_;
                            v___y_2175_ = v_a_2196_;
                            v___y_2176_ = v___x_2198_;
                            v_a_2177_ = v_a_2200_;
                            state = 4;
                            continue;
                        } else {
                            v_val_2201_ = lean_ctor_get(v_quotContext_x3f_2189_, 0);
                            lean_inc(v_val_2201_);
                            v___y_2173_ = v___y_2192_;
                            v___y_2174_ = v___x_2197_;
                            v___y_2175_ = v_a_2196_;
                            v___y_2176_ = v___x_2198_;
                            v_a_2177_ = v_val_2201_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2194_);
                        lean_dec_ref(v___y_2192_);
                        lean_del_object(v___x_2058_);
                        lean_dec(v_a_2056_);
                        lean_dec(v_k_2048_);
                        lean_dec(v_attrKind_2046_);
                        lean_dec(v_doc_x3f_2044_);
                        v_a_2202_ = lean_ctor_get(v___x_2195_, 0);
                        v_isSharedCheck_2209_ = (!lean_is_exclusive(v___x_2195_)) as u8;
                        if v_isSharedCheck_2209_ == 0 {
                            v___x_2204_ = v___x_2195_;
                            v_isShared_2205_ = v_isSharedCheck_2209_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2202_);
                            lean_dec(v___x_2195_);
                            v___x_2204_ = lean_box(0);
                            v_isShared_2205_ = v_isSharedCheck_2209_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2192_);
                    lean_del_object(v___x_2058_);
                    lean_dec(v_a_2056_);
                    lean_dec(v_k_2048_);
                    lean_dec(v_attrKind_2046_);
                    lean_dec(v_doc_x3f_2044_);
                    return v___x_2193_;
                }
            }
            6 => {
                if v_isShared_2205_ == 0 {
                    v___x_2207_ = v___x_2204_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
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
                lean_inc_n(v___x_2210_, 2);
                v___x_2215_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2215_, 0, v___x_2210_);
                lean_ctor_set(v___x_2215_, 1, v___x_2213_);
                lean_inc(v_k_2048_);
                v___x_2216_ = lean_mk_syntax_ident(v_k_2048_);
                v___x_2217_ =
                    l_Lean_Syntax_node2(v___x_2210_, v___x_2214_, v___x_2215_, v___x_2216_);
                lean_inc(v_attrKind_2046_);
                v___x_2218_ =
                    l_Lean_Syntax_node2(v___x_2210_, v___x_2212_, v_attrKind_2046_, v___x_2217_);
                if lean_obj_tag(v_attrs_x3f_2045_) == 0 {
                    v___x_2219_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2220_ = lean_unsigned_to_nat(1);
                    v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
                    v___x_2222_ = lean_array_push(v___x_2221_, v___x_2218_);
                    v___x_2223_ = l_Lean_Syntax_SepArray_ofElems(v___x_2219_, v___x_2222_);
                    lean_dec_ref(v___x_2222_);
                    v___y_2192_ = v___x_2223_;
                    state = 5;
                    continue;
                } else {
                    v_val_2224_ = lean_ctor_get(v_attrs_x3f_2045_, 0);
                    v___x_2225_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2226_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_2224_);
                    v___x_2227_ = lean_array_push(v___x_2226_, v___x_2218_);
                    v___x_2228_ = l_Lean_Syntax_SepArray_ofElems(v___x_2225_, v___x_2227_);
                    lean_dec_ref(v___x_2227_);
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
                    v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
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
                    v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
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
    mut v_doc_x3f_2247_: *mut LeanObject,
    mut v_attrs_x3f_2248_: *mut LeanObject,
    mut v_attrKind_2249_: *mut LeanObject,
    mut v_tk_2250_: *mut LeanObject,
    mut v_k_2251_: *mut LeanObject,
    mut v_alts_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
    mut v_a_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2256_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2254_);
    lean_dec_ref(v_a_2253_);
    lean_dec(v_tk_2250_);
    lean_dec(v_attrs_x3f_2248_);
    return v_res_2256_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(
    mut v_00_u03b1_2257_: *mut LeanObject,
    mut v_ref_2258_: *mut LeanObject,
    mut v_msg_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___redArg(
        v_ref_2258_,
        v_msg_2259_,
        v___y_2260_,
        v___y_2261_,
    );
    return v___x_2263_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1___boxed(
    mut v_00_u03b1_2264_: *mut LeanObject,
    mut v_ref_2265_: *mut LeanObject,
    mut v_msg_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
    mut v___y_2268_: *mut LeanObject,
    mut v___y_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2270_: *mut LeanObject = core::ptr::null_mut();
    v_res_2270_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1(
        v_00_u03b1_2264_,
        v_ref_2265_,
        v_msg_2266_,
        v___y_2267_,
        v___y_2268_,
    );
    lean_dec(v___y_2268_);
    lean_dec_ref(v___y_2267_);
    lean_dec(v_ref_2265_);
    return v_res_2270_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(
    mut v_msgData_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2275_: *mut LeanObject = core::ptr::null_mut();
    v___x_2275_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___redArg(v_msgData_2271_, v___y_2273_);
    return v___x_2275_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_2276_: *mut LeanObject,
    mut v___y_2277_: *mut LeanObject,
    mut v___y_2278_: *mut LeanObject,
    mut v___y_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2280_: *mut LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__3(v_msgData_2276_, v___y_2277_, v___y_2278_);
    lean_dec(v___y_2278_);
    lean_dec_ref(v___y_2277_);
    return v_res_2280_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(
    mut v_00_u03b1_2281_: *mut LeanObject,
    mut v_msg_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    v___x_2286_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___redArg(v_msg_2282_, v___y_2283_, v___y_2284_);
    return v___x_2286_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1___boxed(
    mut v_00_u03b1_2287_: *mut LeanObject,
    mut v_msg_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2292_: *mut LeanObject = core::ptr::null_mut();
    v_res_2292_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1(v_00_u03b1_2287_, v_msg_2288_, v___y_2289_, v___y_2290_);
    lean_dec(v___y_2290_);
    lean_dec_ref(v___y_2289_);
    return v_res_2292_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(
    mut v_msgData_2293_: *mut LeanObject,
    mut v_macroStack_2294_: *mut LeanObject,
    mut v___y_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    v___x_2298_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___redArg(v_msgData_2293_, v_macroStack_2294_, v___y_2296_);
    return v___x_2298_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4___boxed(
    mut v_msgData_2299_: *mut LeanObject,
    mut v_macroStack_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2304_: *mut LeanObject = core::ptr::null_mut();
    v_res_2304_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Command_elabMacroRulesAux_spec__1_spec__1_spec__4(v_msgData_2299_, v_macroStack_2300_, v___y_2301_, v___y_2302_);
    lean_dec(v___y_2302_);
    lean_dec_ref(v___y_2301_);
    return v_res_2304_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(
    mut v___y_2305_: *mut LeanObject,
    mut v_isExporting_2306_: u8,
    mut v_a_x3f_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2323_: u8 = 0;
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2309_ = lean_st_ref_take(v___y_2305_);
                v_env_2310_ = lean_ctor_get(v___x_2309_, 0);
                v_messages_2311_ = lean_ctor_get(v___x_2309_, 1);
                v_scopes_2312_ = lean_ctor_get(v___x_2309_, 2);
                v_usedQuotCtxts_2313_ = lean_ctor_get(v___x_2309_, 3);
                v_nextMacroScope_2314_ = lean_ctor_get(v___x_2309_, 4);
                v_maxRecDepth_2315_ = lean_ctor_get(v___x_2309_, 5);
                v_ngen_2316_ = lean_ctor_get(v___x_2309_, 6);
                v_auxDeclNGen_2317_ = lean_ctor_get(v___x_2309_, 7);
                v_infoState_2318_ = lean_ctor_get(v___x_2309_, 8);
                v_traceState_2319_ = lean_ctor_get(v___x_2309_, 9);
                v_snapshotTasks_2320_ = lean_ctor_get(v___x_2309_, 10);
                v_isSharedCheck_2331_ = (!lean_is_exclusive(v___x_2309_)) as u8;
                if v_isSharedCheck_2331_ == 0 {
                    v___x_2322_ = v___x_2309_;
                    v_isShared_2323_ = v_isSharedCheck_2331_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2320_);
                    lean_inc(v_traceState_2319_);
                    lean_inc(v_infoState_2318_);
                    lean_inc(v_auxDeclNGen_2317_);
                    lean_inc(v_ngen_2316_);
                    lean_inc(v_maxRecDepth_2315_);
                    lean_inc(v_nextMacroScope_2314_);
                    lean_inc(v_usedQuotCtxts_2313_);
                    lean_inc(v_scopes_2312_);
                    lean_inc(v_messages_2311_);
                    lean_inc(v_env_2310_);
                    lean_dec(v___x_2309_);
                    v___x_2322_ = lean_box(0);
                    v_isShared_2323_ = v_isSharedCheck_2331_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2324_ = l_Lean_Environment_setExporting(v_env_2310_, v_isExporting_2306_);
                if v_isShared_2323_ == 0 {
                    lean_ctor_set(v___x_2322_, 0, v___x_2324_);
                    v___x_2326_ = v___x_2322_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2324_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_messages_2311_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 2, v_scopes_2312_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 3, v_usedQuotCtxts_2313_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 4, v_nextMacroScope_2314_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 5, v_maxRecDepth_2315_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 6, v_ngen_2316_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 7, v_auxDeclNGen_2317_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 8, v_infoState_2318_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 9, v_traceState_2319_);
                    lean_ctor_set(v_reuseFailAlloc_2330_, 10, v_snapshotTasks_2320_);
                    v___x_2326_ = v_reuseFailAlloc_2330_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2327_ = lean_st_ref_set(v___y_2305_, v___x_2326_);
                v___x_2328_ = lean_box(0);
                v___x_2329_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2329_, 0, v___x_2328_);
                return v___x_2329_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0___boxed(
    mut v___y_2332_: *mut LeanObject,
    mut v_isExporting_2333_: *mut LeanObject,
    mut v_a_x3f_2334_: *mut LeanObject,
    mut v___y_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_2336_: u8 = 0;
    let mut v_res_2337_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2336_ = (lean_unbox(v_isExporting_2333_) as u8);
    v_res_2337_ =
        l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(
            v___y_2332_,
            v_isExporting_boxed_2336_,
            v_a_x3f_2334_,
        );
    lean_dec(v_a_x3f_2334_);
    lean_dec(v___y_2332_);
    return v_res_2337_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(
    mut v_x_2338_: *mut LeanObject,
    mut v_isExporting_2339_: u8,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2345_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2360_: u8 = 0;
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_unused_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut v_a_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v___x_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2392_: u8 = 0;
    let mut v_unused_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2343_ = lean_st_ref_get(v___y_2341_);
                v_env_2344_ = lean_ctor_get(v___x_2343_, 0);
                lean_inc_ref(v_env_2344_);
                lean_dec(v___x_2343_);
                v_isExporting_2345_ = lean_ctor_get_uint8(
                    v_env_2344_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_2344_);
                v___x_2346_ = lean_st_ref_take(v___y_2341_);
                v_env_2347_ = lean_ctor_get(v___x_2346_, 0);
                v_messages_2348_ = lean_ctor_get(v___x_2346_, 1);
                v_scopes_2349_ = lean_ctor_get(v___x_2346_, 2);
                v_usedQuotCtxts_2350_ = lean_ctor_get(v___x_2346_, 3);
                v_nextMacroScope_2351_ = lean_ctor_get(v___x_2346_, 4);
                v_maxRecDepth_2352_ = lean_ctor_get(v___x_2346_, 5);
                v_ngen_2353_ = lean_ctor_get(v___x_2346_, 6);
                v_auxDeclNGen_2354_ = lean_ctor_get(v___x_2346_, 7);
                v_infoState_2355_ = lean_ctor_get(v___x_2346_, 8);
                v_traceState_2356_ = lean_ctor_get(v___x_2346_, 9);
                v_snapshotTasks_2357_ = lean_ctor_get(v___x_2346_, 10);
                v_isSharedCheck_2395_ = (!lean_is_exclusive(v___x_2346_)) as u8;
                if v_isSharedCheck_2395_ == 0 {
                    v___x_2359_ = v___x_2346_;
                    v_isShared_2360_ = v_isSharedCheck_2395_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_2357_);
                    lean_inc(v_traceState_2356_);
                    lean_inc(v_infoState_2355_);
                    lean_inc(v_auxDeclNGen_2354_);
                    lean_inc(v_ngen_2353_);
                    lean_inc(v_maxRecDepth_2352_);
                    lean_inc(v_nextMacroScope_2351_);
                    lean_inc(v_usedQuotCtxts_2350_);
                    lean_inc(v_scopes_2349_);
                    lean_inc(v_messages_2348_);
                    lean_inc(v_env_2347_);
                    lean_dec(v___x_2346_);
                    v___x_2359_ = lean_box(0);
                    v_isShared_2360_ = v_isSharedCheck_2395_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2361_ = l_Lean_Environment_setExporting(v_env_2347_, v_isExporting_2339_);
                if v_isShared_2360_ == 0 {
                    lean_ctor_set(v___x_2359_, 0, v___x_2361_);
                    v___x_2363_ = v___x_2359_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2361_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_messages_2348_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 2, v_scopes_2349_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 3, v_usedQuotCtxts_2350_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 4, v_nextMacroScope_2351_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 5, v_maxRecDepth_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 6, v_ngen_2353_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 7, v_auxDeclNGen_2354_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 8, v_infoState_2355_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 9, v_traceState_2356_);
                    lean_ctor_set(v_reuseFailAlloc_2394_, 10, v_snapshotTasks_2357_);
                    v___x_2363_ = v_reuseFailAlloc_2394_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2364_ = lean_st_ref_set(v___y_2341_, v___x_2363_);
                lean_inc(v___y_2341_);
                lean_inc_ref(v___y_2340_);
                v_r_2365_ = lean_apply_3(v_x_2338_, v___y_2340_, v___y_2341_, lean_box(0));
                if lean_obj_tag(v_r_2365_) == 0 {
                    v_a_2366_ = lean_ctor_get(v_r_2365_, 0);
                    v_isSharedCheck_2382_ = (!lean_is_exclusive(v_r_2365_)) as u8;
                    if v_isSharedCheck_2382_ == 0 {
                        v___x_2368_ = v_r_2365_;
                        v_isShared_2369_ = v_isSharedCheck_2382_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2366_);
                        lean_dec(v_r_2365_);
                        v___x_2368_ = lean_box(0);
                        v_isShared_2369_ = v_isSharedCheck_2382_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_2383_ = lean_ctor_get(v_r_2365_, 0);
                    lean_inc(v_a_2383_);
                    lean_dec_ref_known(v_r_2365_, 1);
                    v___x_2384_ = lean_box(0);
                    v___x_2385_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_2341_, v_isExporting_2345_, v___x_2384_);
                    v_isSharedCheck_2392_ = (!lean_is_exclusive(v___x_2385_)) as u8;
                    if v_isSharedCheck_2392_ == 0 {
                        v_unused_2393_ = lean_ctor_get(v___x_2385_, 0);
                        lean_dec(v_unused_2393_);
                        v___x_2387_ = v___x_2385_;
                        v_isShared_2388_ = v_isSharedCheck_2392_;
                        state = 7;
                        continue;
                    } else {
                        lean_dec(v___x_2385_);
                        v___x_2387_ = lean_box(0);
                        v_isShared_2388_ = v_isSharedCheck_2392_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                lean_inc(v_a_2366_);
                if v_isShared_2369_ == 0 {
                    lean_ctor_set_tag(v___x_2368_, 1);
                    v___x_2371_ = v___x_2368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2366_);
                    v___x_2371_ = v_reuseFailAlloc_2381_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2372_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg___lam__0(v___y_2341_, v_isExporting_2345_, v___x_2371_);
                lean_dec_ref(v___x_2371_);
                v_isSharedCheck_2379_ = (!lean_is_exclusive(v___x_2372_)) as u8;
                if v_isSharedCheck_2379_ == 0 {
                    v_unused_2380_ = lean_ctor_get(v___x_2372_, 0);
                    lean_dec(v_unused_2380_);
                    v___x_2374_ = v___x_2372_;
                    v_isShared_2375_ = v_isSharedCheck_2379_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_2372_);
                    v___x_2374_ = lean_box(0);
                    v_isShared_2375_ = v_isSharedCheck_2379_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2375_ == 0 {
                    lean_ctor_set(v___x_2374_, 0, v_a_2366_);
                    v___x_2377_ = v___x_2374_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2366_);
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
                    lean_ctor_set_tag(v___x_2387_, 1);
                    lean_ctor_set(v___x_2387_, 0, v_a_2383_);
                    v___x_2390_ = v___x_2387_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2383_);
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
    mut v_x_2396_: *mut LeanObject,
    mut v_isExporting_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_2401_: u8 = 0;
    let mut v_res_2402_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2401_ = (lean_unbox(v_isExporting_2397_) as u8);
    v_res_2402_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(
        v_x_2396_,
        v_isExporting_boxed_2401_,
        v___y_2398_,
        v___y_2399_,
    );
    lean_dec(v___y_2399_);
    lean_dec_ref(v___y_2398_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(
    mut v_00_u03b1_2403_: *mut LeanObject,
    mut v_x_2404_: *mut LeanObject,
    mut v_isExporting_2405_: u8,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(
        v_x_2404_,
        v_isExporting_2405_,
        v___y_2406_,
        v___y_2407_,
    );
    return v___x_2409_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___boxed(
    mut v_00_u03b1_2410_: *mut LeanObject,
    mut v_x_2411_: *mut LeanObject,
    mut v_isExporting_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
    mut v___y_2415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isExporting_boxed_2416_: u8 = 0;
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_2416_ = (lean_unbox(v_isExporting_2412_) as u8);
    v_res_2417_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0(
        v_00_u03b1_2410_,
        v_x_2411_,
        v_isExporting_boxed_2416_,
        v___y_2413_,
        v___y_2414_,
    );
    lean_dec(v___y_2414_);
    lean_dec_ref(v___y_2413_);
    return v_res_2417_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__0(
    mut v___x_2418_: *mut LeanObject,
    mut v___x_2419_: *mut LeanObject,
    mut v_doc_x3f_2420_: *mut LeanObject,
    mut v_attrs_x3f_2421_: *mut LeanObject,
    mut v_attrKind_2422_: *mut LeanObject,
    mut v_tk_2423_: *mut LeanObject,
    mut v_alts_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2439_: u8 = 0;
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2442_: u8 = 0;
    let mut v_ref_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut v_reuseFailAlloc_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2458_: u8 = 0;
    let mut v_unused_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Lean_Elab_Command_getRef___redArg(v___y_2425_);
                if lean_obj_tag(v___x_2428_) == 0 {
                    v_a_2429_ = lean_ctor_get(v___x_2428_, 0);
                    lean_inc(v_a_2429_);
                    lean_dec_ref_known(v___x_2428_, 1);
                    v_fileName_2430_ = lean_ctor_get(v___y_2425_, 0);
                    v_fileMap_2431_ = lean_ctor_get(v___y_2425_, 1);
                    v_currRecDepth_2432_ = lean_ctor_get(v___y_2425_, 2);
                    v_cmdPos_2433_ = lean_ctor_get(v___y_2425_, 3);
                    v_macroStack_2434_ = lean_ctor_get(v___y_2425_, 4);
                    v_quotContext_x3f_2435_ = lean_ctor_get(v___y_2425_, 5);
                    v_currMacroScope_2436_ = lean_ctor_get(v___y_2425_, 6);
                    v_snap_x3f_2437_ = lean_ctor_get(v___y_2425_, 8);
                    v_cancelTk_x3f_2438_ = lean_ctor_get(v___y_2425_, 9);
                    v_suppressElabErrors_2439_ = lean_ctor_get_uint8(
                        v___y_2425_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_isSharedCheck_2458_ = (!lean_is_exclusive(v___y_2425_)) as u8;
                    if v_isSharedCheck_2458_ == 0 {
                        v_unused_2459_ = lean_ctor_get(v___y_2425_, 7);
                        lean_dec(v_unused_2459_);
                        v___x_2441_ = v___y_2425_;
                        v_isShared_2442_ = v_isSharedCheck_2458_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_cancelTk_x3f_2438_);
                        lean_inc(v_snap_x3f_2437_);
                        lean_inc(v_currMacroScope_2436_);
                        lean_inc(v_quotContext_x3f_2435_);
                        lean_inc(v_macroStack_2434_);
                        lean_inc(v_cmdPos_2433_);
                        lean_inc(v_currRecDepth_2432_);
                        lean_inc(v_fileMap_2431_);
                        lean_inc(v_fileName_2430_);
                        lean_dec(v___y_2425_);
                        v___x_2441_ = lean_box(0);
                        v_isShared_2442_ = v_isSharedCheck_2458_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_2425_);
                    lean_dec_ref(v_alts_2424_);
                    lean_dec(v_attrKind_2422_);
                    lean_dec(v_doc_x3f_2420_);
                    lean_dec(v___x_2419_);
                    return v___x_2428_;
                }
            }
            1 => {
                v_ref_2443_ = l_Lean_replaceRef(v___x_2418_, v_a_2429_);
                lean_dec(v_a_2429_);
                if v_isShared_2442_ == 0 {
                    lean_ctor_set(v___x_2441_, 7, v_ref_2443_);
                    v___x_2445_ = v___x_2441_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_fileName_2430_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 1, v_fileMap_2431_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 2, v_currRecDepth_2432_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 3, v_cmdPos_2433_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 4, v_macroStack_2434_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 5, v_quotContext_x3f_2435_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 6, v_currMacroScope_2436_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 7, v_ref_2443_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 8, v_snap_x3f_2437_);
                    lean_ctor_set(v_reuseFailAlloc_2457_, 9, v_cancelTk_x3f_2438_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2457_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
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
                if lean_obj_tag(v___x_2446_) == 0 {
                    v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
                    lean_inc(v_a_2447_);
                    lean_dec_ref_known(v___x_2446_, 1);
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
                    lean_dec_ref(v___x_2445_);
                    return v___x_2448_;
                } else {
                    lean_dec_ref(v___x_2445_);
                    lean_dec_ref(v_alts_2424_);
                    lean_dec(v_attrKind_2422_);
                    lean_dec(v_doc_x3f_2420_);
                    v_a_2449_ = lean_ctor_get(v___x_2446_, 0);
                    v_isSharedCheck_2456_ = (!lean_is_exclusive(v___x_2446_)) as u8;
                    if v_isSharedCheck_2456_ == 0 {
                        v___x_2451_ = v___x_2446_;
                        v_isShared_2452_ = v_isSharedCheck_2456_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2449_);
                        lean_dec(v___x_2446_);
                        v___x_2451_ = lean_box(0);
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
                    v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
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
    mut v___x_2460_: *mut LeanObject,
    mut v___x_2461_: *mut LeanObject,
    mut v_doc_x3f_2462_: *mut LeanObject,
    mut v_attrs_x3f_2463_: *mut LeanObject,
    mut v_attrKind_2464_: *mut LeanObject,
    mut v_tk_2465_: *mut LeanObject,
    mut v_alts_2466_: *mut LeanObject,
    mut v___y_2467_: *mut LeanObject,
    mut v___y_2468_: *mut LeanObject,
    mut v___y_2469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2470_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2468_);
    lean_dec(v_tk_2465_);
    lean_dec(v_attrs_x3f_2463_);
    lean_dec(v___x_2460_);
    return v_res_2470_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__5(
    mut v___x_2474_: *mut LeanObject,
    mut v___x_2475_: *mut LeanObject,
    mut v_attrKind_2476_: *mut LeanObject,
    mut v___x_2477_: *mut LeanObject,
    mut v___x_2478_: *mut LeanObject,
    mut v_attrs_x3f_2479_: *mut LeanObject,
    mut v___x_2480_: *mut LeanObject,
    mut v___x_2481_: *mut LeanObject,
    mut v___x_2482_: *mut LeanObject,
    mut v_doc_x3f_2483_: *mut LeanObject,
    mut v_kind_x3f_2484_: *mut LeanObject,
    mut v_alts_2485_: *mut LeanObject,
    mut v___y_2486_: *mut LeanObject,
    mut v___y_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2494_: u8 = 0;
    let mut v_quotContext_x3f_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: u8 = 0;
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2523_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___y_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2540_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut v_unused_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2564_: u8 = 0;
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2568_: u8 = 0;
    let mut v_a_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2572_: u8 = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2489_ = l_Lean_Elab_Command_getRef___redArg(v___y_2486_);
                if lean_obj_tag(v___x_2489_) == 0 {
                    v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
                    lean_inc(v_a_2490_);
                    lean_dec_ref_known(v___x_2489_, 1);
                    v___x_2491_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2486_);
                    if lean_obj_tag(v___x_2491_) == 0 {
                        v_isSharedCheck_2559_ = (!lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2559_ == 0 {
                            v_unused_2560_ = lean_ctor_get(v___x_2491_, 0);
                            lean_dec(v_unused_2560_);
                            v___x_2493_ = v___x_2491_;
                            v_isShared_2494_ = v_isSharedCheck_2559_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2491_);
                            v___x_2493_ = lean_box(0);
                            v_isShared_2494_ = v_isSharedCheck_2559_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2490_);
                        lean_dec(v_kind_x3f_2484_);
                        lean_dec(v_doc_x3f_2483_);
                        lean_dec_ref(v___x_2482_);
                        lean_dec_ref(v___x_2481_);
                        lean_dec_ref(v___x_2480_);
                        lean_dec_ref(v___x_2477_);
                        lean_dec(v_attrKind_2476_);
                        lean_dec(v___x_2475_);
                        lean_dec(v___x_2474_);
                        v_a_2561_ = lean_ctor_get(v___x_2491_, 0);
                        v_isSharedCheck_2568_ = (!lean_is_exclusive(v___x_2491_)) as u8;
                        if v_isSharedCheck_2568_ == 0 {
                            v___x_2563_ = v___x_2491_;
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2561_);
                            lean_dec(v___x_2491_);
                            v___x_2563_ = lean_box(0);
                            v_isShared_2564_ = v_isSharedCheck_2568_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_kind_x3f_2484_);
                    lean_dec(v_doc_x3f_2483_);
                    lean_dec_ref(v___x_2482_);
                    lean_dec_ref(v___x_2481_);
                    lean_dec_ref(v___x_2480_);
                    lean_dec_ref(v___x_2477_);
                    lean_dec(v_attrKind_2476_);
                    lean_dec(v___x_2475_);
                    lean_dec(v___x_2474_);
                    v_a_2569_ = lean_ctor_get(v___x_2489_, 0);
                    v_isSharedCheck_2576_ = (!lean_is_exclusive(v___x_2489_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2571_ = v___x_2489_;
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_2569_);
                        lean_dec(v___x_2489_);
                        v___x_2571_ = lean_box(0);
                        v_isShared_2572_ = v_isSharedCheck_2576_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_x3f_2495_ = lean_ctor_get(v___y_2486_, 5);
                v___x_2496_ = 0;
                v___x_2497_ = l_Lean_SourceInfo_fromRef(v_a_2490_, v___x_2496_);
                lean_dec(v_a_2490_);
                if lean_obj_tag(v_quotContext_x3f_2495_) == 0 {
                    v___x_2558_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_2487_);
                    lean_dec_ref(v___x_2558_);
                    state = 6;
                    continue;
                } else {
                    state = 6;
                    continue;
                }
            }
            2 => {
                lean_inc_ref_n(v___y_2503_, 2);
                v___x_2505_ = l_Array_append___redArg(v___y_2503_, v___y_2504_);
                lean_dec_ref(v___y_2504_);
                lean_inc_n(v___y_2502_, 2);
                lean_inc_n(v___x_2497_, 3);
                v___x_2506_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2506_, 0, v___x_2497_);
                lean_ctor_set(v___x_2506_, 1, v___y_2502_);
                lean_ctor_set(v___x_2506_, 2, v___x_2505_);
                v___x_2507_ = l_Array_append___redArg(v___y_2503_, v_alts_2485_);
                v___x_2508_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2508_, 0, v___x_2497_);
                lean_ctor_set(v___x_2508_, 1, v___y_2502_);
                lean_ctor_set(v___x_2508_, 2, v___x_2507_);
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
                    lean_ctor_set(v___x_2493_, 0, v___x_2510_);
                    v___x_2512_ = v___x_2493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
                    v___x_2512_ = v_reuseFailAlloc_2513_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2512_;
            }
            4 => {
                lean_inc_ref(v___y_2517_);
                v___x_2519_ = l_Array_append___redArg(v___y_2517_, v___y_2518_);
                lean_dec_ref(v___y_2518_);
                lean_inc(v___y_2516_);
                lean_inc_n(v___x_2497_, 2);
                v___x_2520_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2520_, 0, v___x_2497_);
                lean_ctor_set(v___x_2520_, 1, v___y_2516_);
                lean_ctor_set(v___x_2520_, 2, v___x_2519_);
                v___x_2521_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2521_, 0, v___x_2497_);
                lean_ctor_set(v___x_2521_, 1, v___x_2477_);
                if lean_obj_tag(v_kind_x3f_2484_) == 0 {
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
                    v_val_2523_ = lean_ctor_get(v_kind_x3f_2484_, 0);
                    lean_inc(v_val_2523_);
                    lean_dec_ref_known(v_kind_x3f_2484_, 1);
                    v___x_2524_ = lean_mk_syntax_ident(v_val_2523_);
                    v___x_2525_ = l_Lean_Elab_Command_elabMacroRules___lam__5___closed__0;
                    lean_inc_n(v___x_2497_, 4);
                    v___x_2526_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2526_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2526_, 1, v___x_2525_);
                    v___x_2527_ = l_Lean_Elab_Command_elabMacroRules___lam__5___closed__1;
                    v___x_2528_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2528_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2528_, 1, v___x_2527_);
                    v___x_2529_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
                    v___x_2530_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2530_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2530_, 1, v___x_2529_);
                    v___x_2531_ = l_Lean_Elab_Command_elabMacroRules___lam__5___closed__2;
                    v___x_2532_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2532_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2532_, 1, v___x_2531_);
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
                lean_inc_ref(v___y_2536_);
                v___x_2538_ = l_Array_append___redArg(v___y_2536_, v___y_2537_);
                lean_dec_ref(v___y_2537_);
                lean_inc(v___y_2535_);
                lean_inc(v___x_2497_);
                v___x_2539_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2539_, 0, v___x_2497_);
                lean_ctor_set(v___x_2539_, 1, v___y_2535_);
                lean_ctor_set(v___x_2539_, 2, v___x_2538_);
                if lean_obj_tag(v_attrs_x3f_2479_) == 1 {
                    v_val_2540_ = lean_ctor_get(v_attrs_x3f_2479_, 0);
                    v___x_2541_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__0;
                    v___x_2542_ =
                        l_Lean_Name_mkStr4(v___x_2480_, v___x_2481_, v___x_2482_, v___x_2541_);
                    v___x_2543_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
                    lean_inc_n(v___x_2497_, 4);
                    v___x_2544_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2544_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2544_, 1, v___x_2543_);
                    lean_inc_ref(v___y_2536_);
                    v___x_2545_ = l_Array_append___redArg(v___y_2536_, v_val_2540_);
                    lean_inc(v___y_2535_);
                    v___x_2546_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2546_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2546_, 1, v___y_2535_);
                    lean_ctor_set(v___x_2546_, 2, v___x_2545_);
                    v___x_2547_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
                    v___x_2548_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_2548_, 0, v___x_2497_);
                    lean_ctor_set(v___x_2548_, 1, v___x_2547_);
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
                    lean_dec_ref(v___x_2482_);
                    lean_dec_ref(v___x_2481_);
                    lean_dec_ref(v___x_2480_);
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
                v___x_2554_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                if lean_obj_tag(v_doc_x3f_2483_) == 1 {
                    v_val_2555_ = lean_ctor_get(v_doc_x3f_2483_, 0);
                    lean_inc(v_val_2555_);
                    lean_dec_ref_known(v_doc_x3f_2483_, 1);
                    v___x_2556_ = l_Array_mkArray1___redArg(v_val_2555_);
                    v___y_2535_ = v___x_2553_;
                    v___y_2536_ = v___x_2554_;
                    v___y_2537_ = v___x_2556_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v_doc_x3f_2483_);
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
                    v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
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
                    v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
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
    mut v___x_2577_: *mut LeanObject,
    mut v___x_2578_: *mut LeanObject,
    mut v_attrKind_2579_: *mut LeanObject,
    mut v___x_2580_: *mut LeanObject,
    mut v___x_2581_: *mut LeanObject,
    mut v_attrs_x3f_2582_: *mut LeanObject,
    mut v___x_2583_: *mut LeanObject,
    mut v___x_2584_: *mut LeanObject,
    mut v___x_2585_: *mut LeanObject,
    mut v_doc_x3f_2586_: *mut LeanObject,
    mut v_kind_x3f_2587_: *mut LeanObject,
    mut v_alts_2588_: *mut LeanObject,
    mut v___y_2589_: *mut LeanObject,
    mut v___y_2590_: *mut LeanObject,
    mut v___y_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2592_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2590_);
    lean_dec_ref(v___y_2589_);
    lean_dec_ref(v_alts_2588_);
    lean_dec(v_attrs_x3f_2582_);
    lean_dec(v___x_2581_);
    return v_res_2592_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___lam__1(
    mut v_stx_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2650_: u8 = 0;
    let mut v___y_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2652_: u8 = 0;
    let mut v___y_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2655_: u8 = 0;
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v___y_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2678_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2754_: u8 = 0;
    let mut v___y_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2779_: u8 = 0;
    let mut v___y_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2786_: u8 = 0;
    let mut v___y_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrKind_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: u8 = 0;
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tk_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: u8 = 0;
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: u8 = 0;
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: u8 = 0;
    let mut v_alts_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: u8 = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: u8 = 0;
    let mut v_alts_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: u8 = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: u8 = 0;
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: u8 = 0;
    let mut v_alts_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: u8 = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: u8 = 0;
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v_alts_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: u8 = 0;
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: u8 = 0;
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: u8 = 0;
    let mut v_alts_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: u8 = 0;
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2952_: u8 = 0;
    let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2970_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: u8 = 0;
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2991_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3008_: u8 = 0;
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3012_: u8 = 0;
    let mut v_a_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3016_: u8 = 0;
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3020_: u8 = 0;
    let mut v_doc_x3f_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: u8 = 0;
    let mut v___x_3028_: u8 = 0;
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: u8 = 0;
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: u8 = 0;
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: u8 = 0;
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__4;
                v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__5;
                v___x_2660_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__0;
                v___x_2661_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1;
                lean_inc(v_stx_2645_);
                v___x_2662_ = l_Lean_Syntax_isOfKind(v_stx_2645_, v___x_2661_);
                if v___x_2662_ == 0 {
                    lean_dec(v_stx_2645_);
                    v___x_2728_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                    return v___x_2728_;
                } else {
                    v___x_2729_ = lean_unsigned_to_nat(0);
                    v___x_3038_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2729_);
                    v___x_3039_ = l_Lean_Syntax_isNone(v___x_3038_);
                    if v___x_3039_ == 0 {
                        v___x_3040_ = lean_unsigned_to_nat(1);
                        lean_inc(v___x_3038_);
                        v___x_3041_ = l_Lean_Syntax_matchesNull(v___x_3038_, v___x_3040_);
                        if v___x_3041_ == 0 {
                            lean_dec(v___x_3038_);
                            lean_dec(v_stx_2645_);
                            v___x_3042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_3042_;
                        } else {
                            v_doc_x3f_3043_ = l_Lean_Syntax_getArg(v___x_3038_, v___x_2729_);
                            lean_dec(v___x_3038_);
                            v___x_3044_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__17;
                            lean_inc(v_doc_x3f_3043_);
                            v___x_3045_ = l_Lean_Syntax_isOfKind(v_doc_x3f_3043_, v___x_3044_);
                            if v___x_3045_ == 0 {
                                lean_dec(v_doc_x3f_3043_);
                                lean_dec(v_stx_2645_);
                                v___x_3046_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                                return v___x_3046_;
                            } else {
                                v___x_3047_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3047_, 0, v_doc_x3f_3043_);
                                v_doc_x3f_3022_ = v___x_3047_;
                                v___y_3023_ = v___y_2646_;
                                v___y_3024_ = v___y_2647_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3038_);
                        v___x_3048_ = lean_box(0);
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
                lean_inc_ref_n(v___y_2676_, 3);
                v___x_2679_ = l_Array_append___redArg(v___y_2676_, v___y_2678_);
                lean_dec_ref(v___y_2678_);
                lean_inc_n(v___y_2670_, 6);
                lean_inc_n(v___y_2669_, 17);
                v___x_2680_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2680_, 0, v___y_2669_);
                lean_ctor_set(v___x_2680_, 1, v___y_2670_);
                lean_ctor_set(v___x_2680_, 2, v___x_2679_);
                v___x_2681_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__0;
                lean_inc_ref_n(v___y_2673_, 2);
                v___x_2682_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2673_, v___x_2681_);
                v___x_2683_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__1;
                v___x_2684_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2684_, 0, v___y_2669_);
                lean_ctor_set(v___x_2684_, 1, v___x_2683_);
                v___x_2685_ = l_Array_append___redArg(v___y_2676_, v___y_2671_);
                lean_dec_ref(v___y_2671_);
                v___x_2686_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2686_, 0, v___y_2669_);
                lean_ctor_set(v___x_2686_, 1, v___y_2670_);
                lean_ctor_set(v___x_2686_, 2, v___x_2685_);
                v___x_2687_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__2;
                v___x_2688_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2688_, 0, v___y_2669_);
                lean_ctor_set(v___x_2688_, 1, v___x_2687_);
                v___x_2689_ = l_Lean_Syntax_node3(
                    v___y_2669_,
                    v___x_2682_,
                    v___x_2684_,
                    v___x_2686_,
                    v___x_2688_,
                );
                v___x_2690_ = l_Lean_Syntax_node1(v___y_2669_, v___y_2670_, v___x_2689_);
                lean_inc_ref(v___y_2667_);
                v___x_2691_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2691_, 0, v___y_2669_);
                lean_ctor_set(v___x_2691_, 1, v___y_2667_);
                v___x_2692_ = l_Lean_TSyntax_getId(v___y_2664_);
                v___x_2693_ = l_Lean_mkIdentFrom(v___y_2668_, v___x_2692_, v___x_2662_);
                lean_dec(v___y_2668_);
                v___x_2694_ =
                    l_Lean_Syntax_node2(v___y_2669_, v___y_2670_, v___x_2693_, v___y_2664_);
                v___x_2695_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__6;
                v___x_2696_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2696_, 0, v___y_2669_);
                lean_ctor_set(v___x_2696_, 1, v___x_2695_);
                v___x_2697_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacroRulesAux___closed__8_once),
                    _init_l_Lean_Elab_Command_elabMacroRulesAux___closed__8,
                );
                v___x_2698_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__9;
                v___x_2699_ = l_Lean_addMacroScope(v___y_2677_, v___x_2698_, v___y_2672_);
                v___x_2700_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__6;
                v___x_2701_ = lean_alloc_ctor(3, 4, (0) as u32);
                lean_ctor_set(v___x_2701_, 0, v___y_2669_);
                lean_ctor_set(v___x_2701_, 1, v___x_2697_);
                lean_ctor_set(v___x_2701_, 2, v___x_2699_);
                lean_ctor_set(v___x_2701_, 3, v___x_2700_);
                v___x_2702_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__10;
                v___x_2703_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2703_, 0, v___y_2669_);
                lean_ctor_set(v___x_2703_, 1, v___x_2702_);
                v___x_2704_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__11;
                v___x_2705_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2673_, v___x_2704_);
                v___x_2706_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2706_, 0, v___y_2669_);
                lean_ctor_set(v___x_2706_, 1, v___x_2704_);
                v___x_2707_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__7;
                v___x_2708_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2673_, v___x_2707_);
                v___x_2709_ = l_Lean_Syntax_node1(v___y_2669_, v___y_2670_, v___y_2665_);
                v___x_2710_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2710_, 0, v___y_2669_);
                lean_ctor_set(v___x_2710_, 1, v___y_2670_);
                lean_ctor_set(v___x_2710_, 2, v___y_2676_);
                v___x_2711_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__13;
                v___x_2712_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2712_, 0, v___y_2669_);
                lean_ctor_set(v___x_2712_, 1, v___x_2711_);
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
                v___x_2715_ = lean_unsigned_to_nat(9);
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
                lean_inc(v___y_2666_);
                v___x_2726_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_2726_, 0, v___y_2669_);
                lean_ctor_set(v___x_2726_, 1, v___y_2666_);
                lean_ctor_set(v___x_2726_, 2, v___x_2725_);
                v___x_2727_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2727_, 0, v___x_2726_);
                return v___x_2727_;
            }
            3 => {
                v___x_2743_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__31;
                v___x_2744_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__32;
                v___x_2745_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__12);
                if lean_obj_tag(v___y_2737_) == 1 {
                    v_val_2746_ = lean_ctor_get(v___y_2737_, 0);
                    lean_inc(v_val_2746_);
                    lean_dec_ref_known(v___y_2737_, 1);
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
                    lean_dec(v___y_2737_);
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
                if lean_obj_tag(v___x_2763_) == 0 {
                    v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
                    lean_inc(v_a_2764_);
                    lean_dec_ref_known(v___x_2763_, 1);
                    v___x_2765_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_2760_);
                    lean_dec_ref(v___y_2760_);
                    if lean_obj_tag(v___x_2765_) == 0 {
                        v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
                        lean_inc(v_a_2766_);
                        lean_dec_ref_known(v___x_2765_, 1);
                        v___x_2767_ = l_Lean_Parser_Command_visibility_ofAttrKind(v___y_2761_);
                        v___x_2768_ = l_Lean_SourceInfo_fromRef(v_a_2764_, v___y_2754_);
                        lean_dec(v_a_2764_);
                        if lean_obj_tag(v___y_2756_) == 0 {
                            v___x_2769_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_2752_);
                            v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
                            lean_inc(v_a_2770_);
                            lean_dec_ref(v___x_2769_);
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
                            v_val_2771_ = lean_ctor_get(v___y_2756_, 0);
                            lean_inc(v_val_2771_);
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
                        lean_dec(v_a_2764_);
                        lean_dec_ref(v___y_2762_);
                        lean_dec(v___y_2761_);
                        lean_dec(v___y_2759_);
                        lean_dec(v___y_2758_);
                        lean_dec_ref(v___y_2757_);
                        lean_dec(v___y_2753_);
                        lean_dec(v___y_2751_);
                        lean_dec(v___y_2750_);
                        v_a_2772_ = lean_ctor_get(v___x_2765_, 0);
                        v_isSharedCheck_2779_ = (!lean_is_exclusive(v___x_2765_)) as u8;
                        if v_isSharedCheck_2779_ == 0 {
                            v___x_2774_ = v___x_2765_;
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2772_);
                            lean_dec(v___x_2765_);
                            v___x_2774_ = lean_box(0);
                            v_isShared_2775_ = v_isSharedCheck_2779_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_2762_);
                    lean_dec(v___y_2761_);
                    lean_dec_ref(v___y_2760_);
                    lean_dec(v___y_2759_);
                    lean_dec(v___y_2758_);
                    lean_dec_ref(v___y_2757_);
                    lean_dec(v___y_2753_);
                    lean_dec(v___y_2751_);
                    lean_dec(v___y_2750_);
                    return v___x_2763_;
                }
            }
            5 => {
                if v_isShared_2775_ == 0 {
                    v___x_2777_ = v___x_2774_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
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
                lean_inc_ref(v___y_2790_);
                v___x_2797_ =
                    l_Lean_Name_mkStr4(v___x_2658_, v___x_2659_, v___y_2790_, v___x_2796_);
                v___x_2798_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__37;
                v___x_2799_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__38;
                lean_inc_n(v___y_2793_, 2);
                v___x_2800_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_2800_, 0, v___y_2793_);
                lean_ctor_set(v___x_2800_, 1, v___x_2798_);
                lean_inc(v___y_2781_);
                v___x_2801_ =
                    l_Lean_Syntax_node2(v___y_2793_, v___x_2799_, v___x_2800_, v___y_2781_);
                lean_inc(v___y_2795_);
                v___x_2802_ =
                    l_Lean_Syntax_node2(v___y_2793_, v___x_2797_, v___y_2795_, v___x_2801_);
                if lean_obj_tag(v___y_2787_) == 0 {
                    v___x_2803_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2804_ = lean_mk_empty_array_with_capacity(v___y_2783_);
                    v___x_2805_ = lean_array_push(v___x_2804_, v___x_2802_);
                    v___x_2806_ = l_Lean_Syntax_SepArray_ofElems(v___x_2803_, v___x_2805_);
                    lean_dec_ref(v___x_2805_);
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
                    v_val_2807_ = lean_ctor_get(v___y_2787_, 0);
                    lean_inc(v_val_2807_);
                    lean_dec_ref_known(v___y_2787_, 1);
                    v___x_2808_ = l_Lean_Elab_Command_elabMacroRulesAux___closed__39;
                    v___x_2809_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_2807_);
                    lean_dec(v_val_2807_);
                    v___x_2810_ = lean_array_push(v___x_2809_, v___x_2802_);
                    v___x_2811_ = l_Lean_Syntax_SepArray_ofElems(v___x_2808_, v___x_2810_);
                    lean_dec_ref(v___x_2810_);
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
                v___x_2818_ = lean_unsigned_to_nat(2);
                v_attrKind_2819_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2818_);
                v___x_2820_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__6;
                v___x_2821_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__9;
                lean_inc(v_attrKind_2819_);
                v___x_2822_ = l_Lean_Syntax_isOfKind(v_attrKind_2819_, v___x_2821_);
                if v___x_2822_ == 0 {
                    lean_dec(v_attrKind_2819_);
                    lean_dec(v_attrs_x3f_2817_);
                    lean_dec(v___y_2813_);
                    lean_dec(v_stx_2645_);
                    v___x_2823_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                    return v___x_2823_;
                } else {
                    v___x_2824_ = lean_unsigned_to_nat(3);
                    v_tk_2825_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2824_);
                    v___x_2826_ = lean_unsigned_to_nat(4);
                    v___x_2827_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2826_);
                    lean_inc(v___x_2827_);
                    v___x_2828_ = l_Lean_Syntax_matchesNull(v___x_2827_, v___x_2729_);
                    if v___x_2828_ == 0 {
                        v___x_2829_ = lean_unsigned_to_nat(5);
                        lean_inc(v___x_2827_);
                        v___x_2830_ = l_Lean_Syntax_matchesNull(v___x_2827_, v___x_2829_);
                        if v___x_2830_ == 0 {
                            lean_dec(v___x_2827_);
                            lean_dec(v_tk_2825_);
                            lean_dec(v_attrKind_2819_);
                            lean_dec(v_attrs_x3f_2817_);
                            lean_dec(v___y_2813_);
                            lean_dec(v_stx_2645_);
                            v___x_2831_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_2831_;
                        } else {
                            v___x_2832_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2829_);
                            lean_dec(v_stx_2645_);
                            v___x_2833_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10;
                            lean_inc(v___x_2832_);
                            v___x_2834_ = l_Lean_Syntax_isOfKind(v___x_2832_, v___x_2833_);
                            if v___x_2834_ == 0 {
                                lean_dec(v___x_2832_);
                                lean_dec(v___x_2827_);
                                lean_dec(v_tk_2825_);
                                lean_dec(v_attrKind_2819_);
                                lean_dec(v_attrs_x3f_2817_);
                                lean_dec(v___y_2813_);
                                v___x_2835_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                                return v___x_2835_;
                            } else {
                                v_kind_2836_ = l_Lean_Syntax_getArg(v___x_2827_, v___x_2824_);
                                lean_dec(v___x_2827_);
                                v___x_2837_ = l_Lean_Syntax_getArg(v___x_2832_, v___x_2729_);
                                lean_dec(v___x_2832_);
                                lean_inc(v___x_2837_);
                                v___x_2838_ = l_Lean_Syntax_matchesNull(v___x_2837_, v___y_2816_);
                                if v___x_2838_ == 0 {
                                    v_alts_2839_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                    lean_dec(v___x_2837_);
                                    v___x_2840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                    v___x_2841_ = lean_box(2);
                                    lean_inc_ref(v_alts_2839_);
                                    v___x_2842_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_2842_, 0, v___x_2841_);
                                    lean_ctor_set(v___x_2842_, 1, v___x_2840_);
                                    lean_ctor_set(v___x_2842_, 2, v_alts_2839_);
                                    v___x_2843_ = lean_mk_empty_array_with_capacity(v___x_2818_);
                                    lean_inc(v_tk_2825_);
                                    v___x_2844_ = lean_array_push(v___x_2843_, v_tk_2825_);
                                    v___x_2845_ = lean_array_push(v___x_2844_, v___x_2842_);
                                    v___x_2846_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_2846_, 0, v___x_2841_);
                                    lean_ctor_set(v___x_2846_, 1, v___x_2840_);
                                    lean_ctor_set(v___x_2846_, 2, v___x_2845_);
                                    v___x_2847_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                    lean_dec(v_kind_2836_);
                                    lean_inc(v_attrKind_2819_);
                                    v___f_2848_ = lean_alloc_closure(
                                        l_Lean_Elab_Command_elabMacroRules___lam__0___boxed
                                            as *mut core::ffi::c_void,
                                        10,
                                        7,
                                    );
                                    lean_closure_set(v___f_2848_, 0, v___x_2846_);
                                    lean_closure_set(v___f_2848_, 1, v___x_2847_);
                                    lean_closure_set(v___f_2848_, 2, v___y_2813_);
                                    lean_closure_set(v___f_2848_, 3, v_attrs_x3f_2817_);
                                    lean_closure_set(v___f_2848_, 4, v_attrKind_2819_);
                                    lean_closure_set(v___f_2848_, 5, v_tk_2825_);
                                    lean_closure_set(v___f_2848_, 6, v_alts_2839_);
                                    if v___x_2822_ == 0 {
                                        lean_dec(v_attrKind_2819_);
                                        v___x_2849_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2848_, v___x_2822_, v___y_2814_, v___y_2815_);
                                        return v___x_2849_;
                                    } else {
                                        v___x_2850_ =
                                            l_Lean_Syntax_getArg(v_attrKind_2819_, v___x_2729_);
                                        lean_dec(v_attrKind_2819_);
                                        lean_inc(v___x_2850_);
                                        v___x_2851_ =
                                            l_Lean_Syntax_matchesNull(v___x_2850_, v___y_2816_);
                                        if v___x_2851_ == 0 {
                                            lean_dec(v___x_2850_);
                                            v___x_2852_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2848_, v___x_2822_, v___y_2814_, v___y_2815_);
                                            return v___x_2852_;
                                        } else {
                                            v___x_2853_ =
                                                l_Lean_Syntax_getArg(v___x_2850_, v___x_2729_);
                                            lean_dec(v___x_2850_);
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
                                    lean_inc(v___x_2858_);
                                    v___x_2860_ = l_Lean_Syntax_isOfKind(v___x_2858_, v___x_2859_);
                                    if v___x_2860_ == 0 {
                                        lean_dec(v___x_2858_);
                                        v_alts_2861_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                        lean_dec(v___x_2837_);
                                        v___x_2862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                        v___x_2863_ = lean_box(2);
                                        lean_inc_ref(v_alts_2861_);
                                        v___x_2864_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_2864_, 0, v___x_2863_);
                                        lean_ctor_set(v___x_2864_, 1, v___x_2862_);
                                        lean_ctor_set(v___x_2864_, 2, v_alts_2861_);
                                        v___x_2865_ =
                                            lean_mk_empty_array_with_capacity(v___x_2818_);
                                        lean_inc(v_tk_2825_);
                                        v___x_2866_ = lean_array_push(v___x_2865_, v_tk_2825_);
                                        v___x_2867_ = lean_array_push(v___x_2866_, v___x_2864_);
                                        v___x_2868_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_2868_, 0, v___x_2863_);
                                        lean_ctor_set(v___x_2868_, 1, v___x_2862_);
                                        lean_ctor_set(v___x_2868_, 2, v___x_2867_);
                                        v___x_2869_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                        lean_dec(v_kind_2836_);
                                        lean_inc(v_attrKind_2819_);
                                        v___f_2870_ = lean_alloc_closure(
                                            l_Lean_Elab_Command_elabMacroRules___lam__0___boxed
                                                as *mut core::ffi::c_void,
                                            10,
                                            7,
                                        );
                                        lean_closure_set(v___f_2870_, 0, v___x_2868_);
                                        lean_closure_set(v___f_2870_, 1, v___x_2869_);
                                        lean_closure_set(v___f_2870_, 2, v___y_2813_);
                                        lean_closure_set(v___f_2870_, 3, v_attrs_x3f_2817_);
                                        lean_closure_set(v___f_2870_, 4, v_attrKind_2819_);
                                        lean_closure_set(v___f_2870_, 5, v_tk_2825_);
                                        lean_closure_set(v___f_2870_, 6, v_alts_2861_);
                                        if v___x_2822_ == 0 {
                                            lean_dec(v_attrKind_2819_);
                                            v___x_2871_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2870_, v___x_2822_, v___y_2814_, v___y_2815_);
                                            return v___x_2871_;
                                        } else {
                                            v___x_2872_ =
                                                l_Lean_Syntax_getArg(v_attrKind_2819_, v___x_2729_);
                                            lean_dec(v_attrKind_2819_);
                                            lean_inc(v___x_2872_);
                                            v___x_2873_ =
                                                l_Lean_Syntax_matchesNull(v___x_2872_, v___y_2816_);
                                            if v___x_2873_ == 0 {
                                                lean_dec(v___x_2872_);
                                                v___x_2874_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2870_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                return v___x_2874_;
                                            } else {
                                                v___x_2875_ =
                                                    l_Lean_Syntax_getArg(v___x_2872_, v___x_2729_);
                                                lean_dec(v___x_2872_);
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
                                        lean_inc(v___x_2880_);
                                        v___x_2881_ =
                                            l_Lean_Syntax_matchesNull(v___x_2880_, v___y_2816_);
                                        if v___x_2881_ == 0 {
                                            lean_dec(v___x_2880_);
                                            lean_dec(v___x_2858_);
                                            v_alts_2882_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                            lean_dec(v___x_2837_);
                                            v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                            v___x_2884_ = lean_box(2);
                                            lean_inc_ref(v_alts_2882_);
                                            v___x_2885_ = lean_alloc_ctor(1, 3, (0) as u32);
                                            lean_ctor_set(v___x_2885_, 0, v___x_2884_);
                                            lean_ctor_set(v___x_2885_, 1, v___x_2883_);
                                            lean_ctor_set(v___x_2885_, 2, v_alts_2882_);
                                            v___x_2886_ =
                                                lean_mk_empty_array_with_capacity(v___x_2818_);
                                            lean_inc(v_tk_2825_);
                                            v___x_2887_ = lean_array_push(v___x_2886_, v_tk_2825_);
                                            v___x_2888_ = lean_array_push(v___x_2887_, v___x_2885_);
                                            v___x_2889_ = lean_alloc_ctor(1, 3, (0) as u32);
                                            lean_ctor_set(v___x_2889_, 0, v___x_2884_);
                                            lean_ctor_set(v___x_2889_, 1, v___x_2883_);
                                            lean_ctor_set(v___x_2889_, 2, v___x_2888_);
                                            v___x_2890_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                            lean_dec(v_kind_2836_);
                                            lean_inc(v_attrKind_2819_);
                                            v___f_2891_ = lean_alloc_closure(
                                                l_Lean_Elab_Command_elabMacroRules___lam__0___boxed
                                                    as *mut core::ffi::c_void,
                                                10,
                                                7,
                                            );
                                            lean_closure_set(v___f_2891_, 0, v___x_2889_);
                                            lean_closure_set(v___f_2891_, 1, v___x_2890_);
                                            lean_closure_set(v___f_2891_, 2, v___y_2813_);
                                            lean_closure_set(v___f_2891_, 3, v_attrs_x3f_2817_);
                                            lean_closure_set(v___f_2891_, 4, v_attrKind_2819_);
                                            lean_closure_set(v___f_2891_, 5, v_tk_2825_);
                                            lean_closure_set(v___f_2891_, 6, v_alts_2882_);
                                            if v___x_2822_ == 0 {
                                                lean_dec(v_attrKind_2819_);
                                                v___x_2892_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2891_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                return v___x_2892_;
                                            } else {
                                                v___x_2893_ = l_Lean_Syntax_getArg(
                                                    v_attrKind_2819_,
                                                    v___x_2729_,
                                                );
                                                lean_dec(v_attrKind_2819_);
                                                lean_inc(v___x_2893_);
                                                v___x_2894_ = l_Lean_Syntax_matchesNull(
                                                    v___x_2893_,
                                                    v___y_2816_,
                                                );
                                                if v___x_2894_ == 0 {
                                                    lean_dec(v___x_2893_);
                                                    v___x_2895_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2891_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                    return v___x_2895_;
                                                } else {
                                                    v___x_2896_ = l_Lean_Syntax_getArg(
                                                        v___x_2893_,
                                                        v___x_2729_,
                                                    );
                                                    lean_dec(v___x_2893_);
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
                                            lean_dec(v___x_2880_);
                                            lean_inc(v___x_2901_);
                                            v___x_2902_ =
                                                l_Lean_Syntax_matchesNull(v___x_2901_, v___y_2816_);
                                            if v___x_2902_ == 0 {
                                                lean_dec(v___x_2901_);
                                                lean_dec(v___x_2858_);
                                                v_alts_2903_ = l_Lean_Syntax_getArgs(v___x_2837_);
                                                lean_dec(v___x_2837_);
                                                v___x_2904_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                                v___x_2905_ = lean_box(2);
                                                lean_inc_ref(v_alts_2903_);
                                                v___x_2906_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                lean_ctor_set(v___x_2906_, 0, v___x_2905_);
                                                lean_ctor_set(v___x_2906_, 1, v___x_2904_);
                                                lean_ctor_set(v___x_2906_, 2, v_alts_2903_);
                                                v___x_2907_ =
                                                    lean_mk_empty_array_with_capacity(v___x_2818_);
                                                lean_inc(v_tk_2825_);
                                                v___x_2908_ =
                                                    lean_array_push(v___x_2907_, v_tk_2825_);
                                                v___x_2909_ =
                                                    lean_array_push(v___x_2908_, v___x_2906_);
                                                v___x_2910_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                lean_ctor_set(v___x_2910_, 0, v___x_2905_);
                                                lean_ctor_set(v___x_2910_, 1, v___x_2904_);
                                                lean_ctor_set(v___x_2910_, 2, v___x_2909_);
                                                v___x_2911_ = l_Lean_TSyntax_getId(v_kind_2836_);
                                                lean_dec(v_kind_2836_);
                                                lean_inc(v_attrKind_2819_);
                                                v___f_2912_ = lean_alloc_closure(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed as *mut core::ffi::c_void, 10, 7);
                                                lean_closure_set(v___f_2912_, 0, v___x_2910_);
                                                lean_closure_set(v___f_2912_, 1, v___x_2911_);
                                                lean_closure_set(v___f_2912_, 2, v___y_2813_);
                                                lean_closure_set(v___f_2912_, 3, v_attrs_x3f_2817_);
                                                lean_closure_set(v___f_2912_, 4, v_attrKind_2819_);
                                                lean_closure_set(v___f_2912_, 5, v_tk_2825_);
                                                lean_closure_set(v___f_2912_, 6, v_alts_2903_);
                                                if v___x_2822_ == 0 {
                                                    lean_dec(v_attrKind_2819_);
                                                    v___x_2913_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2912_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                    return v___x_2913_;
                                                } else {
                                                    v___x_2914_ = l_Lean_Syntax_getArg(
                                                        v_attrKind_2819_,
                                                        v___x_2729_,
                                                    );
                                                    lean_dec(v_attrKind_2819_);
                                                    lean_inc(v___x_2914_);
                                                    v___x_2915_ = l_Lean_Syntax_matchesNull(
                                                        v___x_2914_,
                                                        v___y_2816_,
                                                    );
                                                    if v___x_2915_ == 0 {
                                                        lean_dec(v___x_2914_);
                                                        v___x_2916_ = l_Lean_withExporting___at___00Lean_Elab_Command_elabMacroRules_spec__0___redArg(v___f_2912_, v___x_2822_, v___y_2814_, v___y_2815_);
                                                        return v___x_2916_;
                                                    } else {
                                                        v___x_2917_ = l_Lean_Syntax_getArg(
                                                            v___x_2914_,
                                                            v___x_2729_,
                                                        );
                                                        lean_dec(v___x_2914_);
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
                                                lean_dec(v___x_2901_);
                                                v___x_2923_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__14;
                                                lean_inc(v___x_2922_);
                                                v___x_2924_ = l_Lean_Syntax_isOfKind(
                                                    v___x_2922_,
                                                    v___x_2923_,
                                                );
                                                if v___x_2924_ == 0 {
                                                    lean_dec(v___x_2922_);
                                                    lean_dec(v___x_2858_);
                                                    v_alts_2925_ =
                                                        l_Lean_Syntax_getArgs(v___x_2837_);
                                                    lean_dec(v___x_2837_);
                                                    v___x_2926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                                    v___x_2927_ = lean_box(2);
                                                    lean_inc_ref(v_alts_2925_);
                                                    v___x_2928_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                    lean_ctor_set(v___x_2928_, 0, v___x_2927_);
                                                    lean_ctor_set(v___x_2928_, 1, v___x_2926_);
                                                    lean_ctor_set(v___x_2928_, 2, v_alts_2925_);
                                                    v___x_2929_ = lean_mk_empty_array_with_capacity(
                                                        v___x_2818_,
                                                    );
                                                    lean_inc(v_tk_2825_);
                                                    v___x_2930_ =
                                                        lean_array_push(v___x_2929_, v_tk_2825_);
                                                    v___x_2931_ =
                                                        lean_array_push(v___x_2930_, v___x_2928_);
                                                    v___x_2932_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                    lean_ctor_set(v___x_2932_, 0, v___x_2927_);
                                                    lean_ctor_set(v___x_2932_, 1, v___x_2926_);
                                                    lean_ctor_set(v___x_2932_, 2, v___x_2931_);
                                                    v___x_2933_ =
                                                        l_Lean_TSyntax_getId(v_kind_2836_);
                                                    lean_dec(v_kind_2836_);
                                                    lean_inc(v_attrKind_2819_);
                                                    v___f_2934_ = lean_alloc_closure(l_Lean_Elab_Command_elabMacroRules___lam__0___boxed as *mut core::ffi::c_void, 10, 7);
                                                    lean_closure_set(v___f_2934_, 0, v___x_2932_);
                                                    lean_closure_set(v___f_2934_, 1, v___x_2933_);
                                                    lean_closure_set(v___f_2934_, 2, v___y_2813_);
                                                    lean_closure_set(
                                                        v___f_2934_,
                                                        3,
                                                        v_attrs_x3f_2817_,
                                                    );
                                                    lean_closure_set(
                                                        v___f_2934_,
                                                        4,
                                                        v_attrKind_2819_,
                                                    );
                                                    lean_closure_set(v___f_2934_, 5, v_tk_2825_);
                                                    lean_closure_set(v___f_2934_, 6, v_alts_2925_);
                                                    if v___x_2822_ == 0 {
                                                        lean_dec(v_attrKind_2819_);
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
                                                        lean_dec(v_attrKind_2819_);
                                                        lean_inc(v___x_2935_);
                                                        v___x_2936_ = l_Lean_Syntax_matchesNull(
                                                            v___x_2935_,
                                                            v___y_2816_,
                                                        );
                                                        if v___x_2936_ == 0 {
                                                            lean_dec(v___x_2935_);
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
                                                            lean_dec(v___x_2935_);
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
                                                    lean_dec(v___x_2837_);
                                                    v___x_2941_ =
                                                        l_Lean_Elab_Command_getRef___redArg(
                                                            v___y_2814_,
                                                        );
                                                    if lean_obj_tag(v___x_2941_) == 0 {
                                                        v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
                                                        lean_inc(v_a_2942_);
                                                        lean_dec_ref_known(v___x_2941_, 1);
                                                        v_fileName_2943_ =
                                                            lean_ctor_get(v___y_2814_, 0);
                                                        v_fileMap_2944_ =
                                                            lean_ctor_get(v___y_2814_, 1);
                                                        v_currRecDepth_2945_ =
                                                            lean_ctor_get(v___y_2814_, 2);
                                                        v_cmdPos_2946_ =
                                                            lean_ctor_get(v___y_2814_, 3);
                                                        v_macroStack_2947_ =
                                                            lean_ctor_get(v___y_2814_, 4);
                                                        v_quotContext_x3f_2948_ =
                                                            lean_ctor_get(v___y_2814_, 5);
                                                        v_currMacroScope_2949_ =
                                                            lean_ctor_get(v___y_2814_, 6);
                                                        v_snap_x3f_2950_ =
                                                            lean_ctor_get(v___y_2814_, 8);
                                                        v_cancelTk_x3f_2951_ =
                                                            lean_ctor_get(v___y_2814_, 9);
                                                        v_suppressElabErrors_2952_ =
                                                            lean_ctor_get_uint8(
                                                                v___y_2814_,
                                                                (core::mem::size_of::<
                                                                    *mut LeanObject,
                                                                >(
                                                                ) * 10)
                                                                    as u32,
                                                            );
                                                        v___x_2953_ = l_Lean_Syntax_getArg(
                                                            v___x_2858_,
                                                            v___x_2824_,
                                                        );
                                                        lean_dec(v___x_2858_);
                                                        v___x_2954_ =
                                                            lean_mk_empty_array_with_capacity(
                                                                v___x_2818_,
                                                            );
                                                        lean_inc(v_tk_2825_);
                                                        v___x_2955_ = lean_array_push(
                                                            v___x_2954_,
                                                            v_tk_2825_,
                                                        );
                                                        lean_inc(v___x_2953_);
                                                        v___x_2956_ = lean_array_push(
                                                            v___x_2955_,
                                                            v___x_2953_,
                                                        );
                                                        v___x_2957_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                                        v___x_2958_ = lean_box(2);
                                                        v___x_2959_ =
                                                            lean_alloc_ctor(1, 3, (0) as u32);
                                                        lean_ctor_set(v___x_2959_, 0, v___x_2958_);
                                                        lean_ctor_set(v___x_2959_, 1, v___x_2957_);
                                                        lean_ctor_set(v___x_2959_, 2, v___x_2956_);
                                                        v_ref_2960_ = l_Lean_replaceRef(
                                                            v___x_2959_,
                                                            v_a_2942_,
                                                        );
                                                        lean_dec(v_a_2942_);
                                                        lean_dec_ref_known(v___x_2959_, 3);
                                                        lean_inc(v_cancelTk_x3f_2951_);
                                                        lean_inc(v_snap_x3f_2950_);
                                                        lean_inc(v_currMacroScope_2949_);
                                                        lean_inc(v_quotContext_x3f_2948_);
                                                        lean_inc(v_macroStack_2947_);
                                                        lean_inc(v_cmdPos_2946_);
                                                        lean_inc(v_currRecDepth_2945_);
                                                        lean_inc_ref(v_fileMap_2944_);
                                                        lean_inc_ref(v_fileName_2943_);
                                                        v___x_2961_ =
                                                            lean_alloc_ctor(0, 10, (1) as u32);
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            0,
                                                            v_fileName_2943_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            1,
                                                            v_fileMap_2944_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            2,
                                                            v_currRecDepth_2945_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            3,
                                                            v_cmdPos_2946_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            4,
                                                            v_macroStack_2947_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            5,
                                                            v_quotContext_x3f_2948_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            6,
                                                            v_currMacroScope_2949_,
                                                        );
                                                        lean_ctor_set(v___x_2961_, 7, v_ref_2960_);
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            8,
                                                            v_snap_x3f_2950_,
                                                        );
                                                        lean_ctor_set(
                                                            v___x_2961_,
                                                            9,
                                                            v_cancelTk_x3f_2951_,
                                                        );
                                                        lean_ctor_set_uint8(
                                                            v___x_2961_,
                                                            (core::mem::size_of::<*mut LeanObject>(
                                                            ) * 10)
                                                                as u32,
                                                            v_suppressElabErrors_2952_,
                                                        );
                                                        v___x_2962_ =
                                                            l_Lean_Elab_Command_getRef___redArg(
                                                                v___x_2961_,
                                                            );
                                                        if lean_obj_tag(v___x_2962_) == 0 {
                                                            v_a_2963_ =
                                                                lean_ctor_get(v___x_2962_, 0);
                                                            lean_inc(v_a_2963_);
                                                            lean_dec_ref_known(v___x_2962_, 1);
                                                            v___x_2964_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_2961_);
                                                            if lean_obj_tag(v___x_2964_) == 0 {
                                                                lean_dec_ref_known(v___x_2964_, 1);
                                                                v___x_2965_ =
                                                                    l_Lean_SourceInfo_fromRef(
                                                                        v_a_2963_,
                                                                        v___x_2828_,
                                                                    );
                                                                lean_dec(v_a_2963_);
                                                                if lean_obj_tag(
                                                                    v_quotContext_x3f_2948_,
                                                                ) == 0
                                                                {
                                                                    v___x_2966_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacroRulesAux_spec__3___redArg(v___y_2815_);
                                                                    lean_dec_ref(v___x_2966_);
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
                                                                lean_dec(v_a_2963_);
                                                                lean_dec_ref_known(v___x_2961_, 10);
                                                                lean_dec(v___x_2953_);
                                                                lean_dec(v___x_2922_);
                                                                lean_dec(v_kind_2836_);
                                                                lean_dec(v_tk_2825_);
                                                                lean_dec(v_attrKind_2819_);
                                                                lean_dec(v_attrs_x3f_2817_);
                                                                lean_dec(v___y_2813_);
                                                                v_a_2967_ =
                                                                    lean_ctor_get(v___x_2964_, 0);
                                                                v_isSharedCheck_2974_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_2964_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_2974_ == 0 {
                                                                    v___x_2969_ = v___x_2964_;
                                                                    v_isShared_2970_ =
                                                                        v_isSharedCheck_2974_;
                                                                    state = 9;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_2967_);
                                                                    lean_dec(v___x_2964_);
                                                                    v___x_2969_ = lean_box(0);
                                                                    v_isShared_2970_ =
                                                                        v_isSharedCheck_2974_;
                                                                    state = 9;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref_known(v___x_2961_, 10);
                                                            lean_dec(v___x_2953_);
                                                            lean_dec(v___x_2922_);
                                                            lean_dec(v_kind_2836_);
                                                            lean_dec(v_tk_2825_);
                                                            lean_dec(v_attrKind_2819_);
                                                            lean_dec(v_attrs_x3f_2817_);
                                                            lean_dec(v___y_2813_);
                                                            return v___x_2962_;
                                                        }
                                                    } else {
                                                        lean_dec(v___x_2922_);
                                                        lean_dec(v___x_2858_);
                                                        lean_dec(v_kind_2836_);
                                                        lean_dec(v_tk_2825_);
                                                        lean_dec(v_attrKind_2819_);
                                                        lean_dec(v_attrs_x3f_2817_);
                                                        lean_dec(v___y_2813_);
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
                        lean_dec(v___x_2827_);
                        v___x_2975_ = lean_unsigned_to_nat(5);
                        v___x_2976_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_2975_);
                        lean_dec(v_stx_2645_);
                        v___x_2977_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__10;
                        lean_inc(v___x_2976_);
                        v___x_2978_ = l_Lean_Syntax_isOfKind(v___x_2976_, v___x_2977_);
                        if v___x_2978_ == 0 {
                            lean_dec(v___x_2976_);
                            lean_dec(v_tk_2825_);
                            lean_dec(v_attrKind_2819_);
                            lean_dec(v_attrs_x3f_2817_);
                            lean_dec(v___y_2813_);
                            v___x_2979_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_2979_;
                        } else {
                            v___x_2980_ = l_Lean_Elab_Command_getRef___redArg(v___y_2814_);
                            if lean_obj_tag(v___x_2980_) == 0 {
                                v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
                                lean_inc(v_a_2981_);
                                lean_dec_ref_known(v___x_2980_, 1);
                                v_fileName_2982_ = lean_ctor_get(v___y_2814_, 0);
                                v_fileMap_2983_ = lean_ctor_get(v___y_2814_, 1);
                                v_currRecDepth_2984_ = lean_ctor_get(v___y_2814_, 2);
                                v_cmdPos_2985_ = lean_ctor_get(v___y_2814_, 3);
                                v_macroStack_2986_ = lean_ctor_get(v___y_2814_, 4);
                                v_quotContext_x3f_2987_ = lean_ctor_get(v___y_2814_, 5);
                                v_currMacroScope_2988_ = lean_ctor_get(v___y_2814_, 6);
                                v_snap_x3f_2989_ = lean_ctor_get(v___y_2814_, 8);
                                v_cancelTk_x3f_2990_ = lean_ctor_get(v___y_2814_, 9);
                                v_suppressElabErrors_2991_ = lean_ctor_get_uint8(
                                    v___y_2814_,
                                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                                );
                                v___x_2992_ = l_Lean_Syntax_getArg(v___x_2976_, v___x_2729_);
                                lean_dec(v___x_2976_);
                                v_alts_2993_ = l_Lean_Syntax_getArgs(v___x_2992_);
                                lean_dec(v___x_2992_);
                                v___x_2994_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacroRulesAux_spec__4___closed__11;
                                v___x_2995_ = lean_box(2);
                                lean_inc_ref(v_alts_2993_);
                                v___x_2996_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_2996_, 0, v___x_2995_);
                                lean_ctor_set(v___x_2996_, 1, v___x_2994_);
                                lean_ctor_set(v___x_2996_, 2, v_alts_2993_);
                                v___f_2997_ = lean_alloc_closure(
                                    l_Lean_Elab_Command_elabMacroRules___lam__5___boxed
                                        as *mut core::ffi::c_void,
                                    15,
                                    10,
                                );
                                lean_closure_set(v___f_2997_, 0, v___x_2977_);
                                lean_closure_set(v___f_2997_, 1, v___x_2661_);
                                lean_closure_set(v___f_2997_, 2, v_attrKind_2819_);
                                lean_closure_set(v___f_2997_, 3, v___x_2660_);
                                lean_closure_set(v___f_2997_, 4, v___x_2729_);
                                lean_closure_set(v___f_2997_, 5, v_attrs_x3f_2817_);
                                lean_closure_set(v___f_2997_, 6, v___x_2658_);
                                lean_closure_set(v___f_2997_, 7, v___x_2659_);
                                lean_closure_set(v___f_2997_, 8, v___x_2820_);
                                lean_closure_set(v___f_2997_, 9, v___y_2813_);
                                v___x_2998_ = lean_mk_empty_array_with_capacity(v___x_2818_);
                                v___x_2999_ = lean_array_push(v___x_2998_, v_tk_2825_);
                                v___x_3000_ = lean_array_push(v___x_2999_, v___x_2996_);
                                v___x_3001_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_3001_, 0, v___x_2995_);
                                lean_ctor_set(v___x_3001_, 1, v___x_2994_);
                                lean_ctor_set(v___x_3001_, 2, v___x_3000_);
                                v_ref_3002_ = l_Lean_replaceRef(v___x_3001_, v_a_2981_);
                                lean_dec(v_a_2981_);
                                lean_dec_ref_known(v___x_3001_, 3);
                                lean_inc(v_cancelTk_x3f_2990_);
                                lean_inc(v_snap_x3f_2989_);
                                lean_inc(v_currMacroScope_2988_);
                                lean_inc(v_quotContext_x3f_2987_);
                                lean_inc(v_macroStack_2986_);
                                lean_inc(v_cmdPos_2985_);
                                lean_inc(v_currRecDepth_2984_);
                                lean_inc_ref(v_fileMap_2983_);
                                lean_inc_ref(v_fileName_2982_);
                                v___x_3003_ = lean_alloc_ctor(0, 10, (1) as u32);
                                lean_ctor_set(v___x_3003_, 0, v_fileName_2982_);
                                lean_ctor_set(v___x_3003_, 1, v_fileMap_2983_);
                                lean_ctor_set(v___x_3003_, 2, v_currRecDepth_2984_);
                                lean_ctor_set(v___x_3003_, 3, v_cmdPos_2985_);
                                lean_ctor_set(v___x_3003_, 4, v_macroStack_2986_);
                                lean_ctor_set(v___x_3003_, 5, v_quotContext_x3f_2987_);
                                lean_ctor_set(v___x_3003_, 6, v_currMacroScope_2988_);
                                lean_ctor_set(v___x_3003_, 7, v_ref_3002_);
                                lean_ctor_set(v___x_3003_, 8, v_snap_x3f_2989_);
                                lean_ctor_set(v___x_3003_, 9, v_cancelTk_x3f_2990_);
                                lean_ctor_set_uint8(
                                    v___x_3003_,
                                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                                    v_suppressElabErrors_2991_,
                                );
                                v___x_3004_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(
                                    v_alts_2993_,
                                    v___x_2660_,
                                    v___f_2997_,
                                    v___x_3003_,
                                    v___y_2815_,
                                );
                                lean_dec_ref_known(v___x_3003_, 10);
                                lean_dec_ref(v_alts_2993_);
                                if lean_obj_tag(v___x_3004_) == 0 {
                                    v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
                                    v_isSharedCheck_3012_ = (!lean_is_exclusive(v___x_3004_)) as u8;
                                    if v_isSharedCheck_3012_ == 0 {
                                        v___x_3007_ = v___x_3004_;
                                        v_isShared_3008_ = v_isSharedCheck_3012_;
                                        state = 11;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3005_);
                                        lean_dec(v___x_3004_);
                                        v___x_3007_ = lean_box(0);
                                        v_isShared_3008_ = v_isSharedCheck_3012_;
                                        state = 11;
                                        continue;
                                    }
                                } else {
                                    v_a_3013_ = lean_ctor_get(v___x_3004_, 0);
                                    v_isSharedCheck_3020_ = (!lean_is_exclusive(v___x_3004_)) as u8;
                                    if v_isSharedCheck_3020_ == 0 {
                                        v___x_3015_ = v___x_3004_;
                                        v_isShared_3016_ = v_isSharedCheck_3020_;
                                        state = 13;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3013_);
                                        lean_dec(v___x_3004_);
                                        v___x_3015_ = lean_box(0);
                                        v_isShared_3016_ = v_isSharedCheck_3020_;
                                        state = 13;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v___x_2976_);
                                lean_dec(v_tk_2825_);
                                lean_dec(v_attrKind_2819_);
                                lean_dec(v_attrs_x3f_2817_);
                                lean_dec(v___y_2813_);
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
                    v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
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
                    v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
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
                    v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
                    v___x_3018_ = v_reuseFailAlloc_3019_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3018_;
            }
            15 => {
                v___x_3025_ = lean_unsigned_to_nat(1);
                v___x_3026_ = l_Lean_Syntax_getArg(v_stx_2645_, v___x_3025_);
                v___x_3027_ = l_Lean_Syntax_isNone(v___x_3026_);
                if v___x_3027_ == 0 {
                    lean_inc(v___x_3026_);
                    v___x_3028_ = l_Lean_Syntax_matchesNull(v___x_3026_, v___x_3025_);
                    if v___x_3028_ == 0 {
                        lean_dec(v___x_3026_);
                        lean_dec(v_doc_x3f_3022_);
                        lean_dec(v_stx_2645_);
                        v___x_3029_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                        return v___x_3029_;
                    } else {
                        v___x_3030_ = l_Lean_Syntax_getArg(v___x_3026_, v___x_2729_);
                        lean_dec(v___x_3026_);
                        v___x_3031_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__15;
                        lean_inc(v___x_3030_);
                        v___x_3032_ = l_Lean_Syntax_isOfKind(v___x_3030_, v___x_3031_);
                        if v___x_3032_ == 0 {
                            lean_dec(v___x_3030_);
                            lean_dec(v_doc_x3f_3022_);
                            lean_dec(v_stx_2645_);
                            v___x_3033_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacroRulesAux_spec__0___redArg();
                            return v___x_3033_;
                        } else {
                            v___x_3034_ = l_Lean_Syntax_getArg(v___x_3030_, v___x_3025_);
                            lean_dec(v___x_3030_);
                            v_attrs_x3f_3035_ = l_Lean_Syntax_getArgs(v___x_3034_);
                            lean_dec(v___x_3034_);
                            v___x_3036_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_3036_, 0, v_attrs_x3f_3035_);
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
                    lean_dec(v___x_3026_);
                    v___x_3037_ = lean_box(0);
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
    mut v_stx_3049_: *mut LeanObject,
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3053_: *mut LeanObject = core::ptr::null_mut();
    v_res_3053_ =
        l_Lean_Elab_Command_elabMacroRules___lam__1(v_stx_3049_, v___y_3050_, v___y_3051_);
    lean_dec(v___y_3051_);
    lean_dec_ref(v___y_3050_);
    return v_res_3053_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules(
    mut v_a_3055_: *mut LeanObject,
    mut v_a_3056_: *mut LeanObject,
    mut v_a_3057_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    v___f_3059_ = l_Lean_Elab_Command_elabMacroRules___closed__0;
    v___x_3060_ = l_Lean_Elab_Command_adaptExpander(v___f_3059_, v_a_3055_, v_a_3056_, v_a_3057_);
    return v___x_3060_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacroRules___boxed(
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3065_: *mut LeanObject = core::ptr::null_mut();
    v_res_3065_ = l_Lean_Elab_Command_elabMacroRules(v_a_3061_, v_a_3062_, v_a_3063_);
    lean_dec(v_a_3063_);
    lean_dec_ref(v_a_3062_);
    return v_res_3065_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1()
-> *mut LeanObject {
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    v___x_3073_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_3074_ = l_Lean_Elab_Command_elabMacroRules___lam__1___closed__1;
    v___x_3075_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1;
    v___x_3076_ = lean_alloc_closure(
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
    mut v_a_3078_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3079_: *mut LeanObject = core::ptr::null_mut();
    v_res_3079_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
    return v_res_3079_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3()
-> *mut LeanObject {
    let mut v___x_3106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    v___x_3106_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1___closed__1;
    v___x_3107_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___closed__6;
    v___x_3108_ = l_Lean_addBuiltinDeclarationRanges(v___x_3106_, v___x_3107_);
    return v___x_3108_;
}
pub unsafe fn l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3___boxed(
    mut v_a_3109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3110_: *mut LeanObject = core::ptr::null_mut();
    v_res_3110_ = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
    return v_res_3110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_MacroRules(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AuxDef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_MacroRules_0__Lean_Elab_Command_elabMacroRules___regBuiltin_Lean_Elab_Command_elabMacroRules_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_MacroRules(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_MacroRules(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_AuxDef(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_MacroRules(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_MacroRules(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_MacroRules(builtin);
}
