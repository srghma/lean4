// Lean compiler output
// Module: Lean.Elab.Macro
// Imports: Lean.Elab.MacroArgUtil
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_unzip___redArg};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_isNone,
    l_Lean_Syntax_mkNameLit, l_Lean_Syntax_mkNumLit, l_Lean_TSyntax_getId,
    l_Lean_evalOptPrio___boxed, l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind,
    l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6, l_Lean_addMacroScope,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef, l_String_toRawSubstring_x27,
    lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_elabCommand,
    l_Lean_Elab_Command_getCurrMacroScope___redArg, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_getScope___redArg,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::MacroArgUtil::{
    initialize_Lean_Elab_MacroArgUtil, l_Lean_Elab_Command_expandMacroArg,
    runtime_initialize_Lean_Elab_MacroArgUtil,
};
use crate::r#gen::Lean::Elab::Syntax::l_Lean_Elab_Command_elabSyntax;
use crate::r#gen::Lean::Elab::Util::{
    l_Lean_Elab_expandMacroImpl_x3f, l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack,
};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::{
    lean_string_append, lean_string_intercalate,
};
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1: usize = 0;
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__10_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__13_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__20_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__0_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__1_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__2_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__3_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__4_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [124, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__5_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [113, 117, 111, 116, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__6_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [96, 40, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__7_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__8_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__9_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__10_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [70, 117, 110, 99, 116, 111, 114, 46, 109, 97, 112, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacro___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacro___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacro___closed__12_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [70, 117, 110, 99, 116, 111, 114, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__13_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [109, 97, 112, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__13_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__12_value)
                as *mut crate::leanh::LeanObject,
            2226500928782199335 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__14_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__14_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__13_value)
                as *mut crate::leanh::LeanObject,
            16332818199912898112 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__15_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__14_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__16_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__15_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__17_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [112, 97, 114, 101, 110, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__18_value: crate::leanh::LeanStringObject<15> =
    crate::leanh::LeanStringObject {
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
            104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__19_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__20_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__19_value)
                as *mut crate::leanh::LeanObject,
            9871775667037945883 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__20_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacro___closed__21_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacro___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacro___closed__22_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__23_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__22_value)
                as *mut crate::leanh::LeanObject,
            11510100434945111860 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__23_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            16981400742628996529 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__24_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__23_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__24_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__25_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__25_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__25_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__26_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__25_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__26_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__27_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [83, 121, 110, 116, 97, 120, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__27_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__28_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__28_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__28_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__27_value)
                as *mut crate::leanh::LeanObject,
            5337926038336999469 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__29_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__28_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__30_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__29_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__30_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__31_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__32_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [64, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__33_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [84, 83, 121, 110, 116, 97, 120, 46, 114, 97, 119, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacro___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacro___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacro___closed__35_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [84, 83, 121, 110, 116, 97, 120, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__36_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [114, 97, 119, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__36_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__37_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__35_value)
                as *mut crate::leanh::LeanObject,
            13976321414845142129 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__37_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__37_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__36_value)
                as *mut crate::leanh::LeanObject,
            7148764482511043314 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__37_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__38_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__38_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__38_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__35_value)
                as *mut crate::leanh::LeanObject,
            432428189503149776 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__38_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__38_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__36_value)
                as *mut crate::leanh::LeanObject,
            5776529165383695719 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__39_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__38_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__40_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__39_value)
                as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__40_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__41_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__41_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__42_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [96, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__43_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [46, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__44_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__44_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__45_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__45_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__45_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__45_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__45_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__45_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__45_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__44_value)
                as *mut crate::leanh::LeanObject,
            15166853502246173068 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__46_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__46_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__47_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__47_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__47_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__47_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__47_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__47_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__47_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__46_value)
                as *mut crate::leanh::LeanObject,
            127604530719969405 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__47_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__48_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__49_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 97, 109, 101, 100, 80, 114, 105, 111, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__49_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__50_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__50_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__50_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__50_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__50_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__50_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__50_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__49_value)
                as *mut crate::leanh::LeanObject,
            13348752267415789739 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__51_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__51_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__52_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [112, 114, 105, 111, 114, 105, 116, 121, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__53_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__54_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__55_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__56_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 99, 111, 112, 101, 100, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__57_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 97, 109, 101, 100, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__57_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__58_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__58_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__58_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__58_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__58_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__58_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__58_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__57_value)
                as *mut crate::leanh::LeanObject,
            17682753938374962505 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__59_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__59_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__60_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [112, 114, 101, 99, 101, 100, 101, 110, 99, 101, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__60_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__61_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__61_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__61_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__61_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__61_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__60_value)
                as *mut crate::leanh::LeanObject,
            11586196343691998021 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__61: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__62_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__62: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__63_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__63: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__64_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__65_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [115, 121, 110, 116, 97, 120, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__65: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__65_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__66_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__66_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__66_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__66_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__66_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__66_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__66_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__65_value)
                as *mut crate::leanh::LeanObject,
            2812521669163367463 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__66: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__66_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabMacro___closed__67_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabMacro___closed__67: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabMacro___closed__68_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [109, 97, 99, 114, 111, 84, 97, 105, 108, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__68: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__68_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__69_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__69_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__69_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__69_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__69_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__69_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__69_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__68_value)
                as *mut crate::leanh::LeanObject,
            3501047195586522559 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__69: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__70_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [110, 117, 108, 108, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__70: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__71_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__70_value)
                as *mut crate::leanh::LeanObject,
            9855511589286918680 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__71: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__71_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__72_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 101, 114, 109, 0],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__72: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__72_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__73_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__73: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__73_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__74_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__74_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__74_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__74_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__74_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__72_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__74_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__74_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__73_value)
                as *mut crate::leanh::LeanObject,
            7983999284776576032 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__74: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__74_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__75_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__75_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__75_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__75_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__75_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__72_value)
                as *mut crate::leanh::LeanObject,
            16572064140653406795 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__75_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__75_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__62_value)
                as *mut crate::leanh::LeanObject,
            2533412339571800130 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__75: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__75_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabMacro___closed__76_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabMacro___closed__76: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__76_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabMacro___closed__77_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__77_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__77_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabMacro___closed__77_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__77_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabMacro___closed__77_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__77_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__76_value)
                as *mut crate::leanh::LeanObject,
            9063780239635860524 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabMacro___closed__77: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__77_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 108, 97, 98, 77, 97, 99, 114, 111, 0]};
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__22_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabMacro___closed__8_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__0_value) as *mut crate::leanh::LeanObject,15334665832227214409 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 44 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 50 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 14 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 63 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2176_ = crate::leanh::lean_box(0);
    v___x_2177_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_2178_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2178_, 0, v___x_2177_);
    crate::leanh::lean_ctor_set(v___x_2178_, 1, v___x_2176_);
    return v___x_2178_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___closed__0);
    v___x_2181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2181_, 0, v___x_2180_);
    return v___x_2181_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg___boxed(
    mut v___y_2182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2183_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
    return v_res_2183_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0(
    mut v_00_u03b1_2184_: *mut crate::leanh::LeanObject,
    mut v___y_2185_: *mut crate::leanh::LeanObject,
    mut v___y_2186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2188_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
    return v___x_2188_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___boxed(
    mut v_00_u03b1_2189_: *mut crate::leanh::LeanObject,
    mut v___y_2190_: *mut crate::leanh::LeanObject,
    mut v___y_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2193_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0(
        v_00_u03b1_2189_,
        v___y_2190_,
        v___y_2191_,
    );
    crate::leanh::lean_dec(v___y_2191_);
    crate::leanh::lean_dec_ref(v___y_2190_);
    return v_res_2193_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(
    mut v___y_2194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2196_ = lean_st_ref_get(v___y_2194_);
    v_env_2197_ = crate::leanh::lean_ctor_get(v___x_2196_, 0);
    crate::leanh::lean_inc_ref(v_env_2197_);
    crate::leanh::lean_dec(v___x_2196_);
    v___x_2198_ = l_Lean_Environment_header(v_env_2197_);
    crate::leanh::lean_dec_ref(v_env_2197_);
    v_mainModule_2199_ = crate::leanh::lean_ctor_get(v___x_2198_, 0);
    crate::leanh::lean_inc(v_mainModule_2199_);
    crate::leanh::lean_dec_ref(v___x_2198_);
    v___x_2200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2200_, 0, v_mainModule_2199_);
    return v___x_2200_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg___boxed(
    mut v___y_2201_: *mut crate::leanh::LeanObject,
    mut v___y_2202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2203_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_2201_);
    crate::leanh::lean_dec(v___y_2201_);
    return v_res_2203_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4(
    mut v___y_2204_: *mut crate::leanh::LeanObject,
    mut v___y_2205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2207_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_2205_);
    return v___x_2207_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___boxed(
    mut v___y_2208_: *mut crate::leanh::LeanObject,
    mut v___y_2209_: *mut crate::leanh::LeanObject,
    mut v___y_2210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2211_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4(v___y_2208_, v___y_2209_);
    crate::leanh::lean_dec(v___y_2209_);
    crate::leanh::lean_dec_ref(v___y_2208_);
    return v_res_2211_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacro___lam__0(
    mut v___y_2212_: *mut crate::leanh::LeanObject,
    mut v___y_2213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2219_: u8 = 0;
    let mut v___x_2220_: u8 = 0;
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2225_: u8 = 0;
    let mut v_a_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2215_ = l_Lean_Elab_Command_getRef___redArg(v___y_2212_);
                if crate::leanh::lean_obj_tag(v___x_2215_) == 0 {
                    v_a_2216_ = crate::leanh::lean_ctor_get(v___x_2215_, 0);
                    v_isSharedCheck_2225_ = (!crate::leanh::lean_is_exclusive(v___x_2215_)) as u8;
                    if v_isSharedCheck_2225_ == 0 {
                        v___x_2218_ = v___x_2215_;
                        v_isShared_2219_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2216_);
                        crate::leanh::lean_dec(v___x_2215_);
                        v___x_2218_ = crate::leanh::lean_box(0);
                        v_isShared_2219_ = v_isSharedCheck_2225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2226_ = crate::leanh::lean_ctor_get(v___x_2215_, 0);
                    v_isSharedCheck_2233_ = (!crate::leanh::lean_is_exclusive(v___x_2215_)) as u8;
                    if v_isSharedCheck_2233_ == 0 {
                        v___x_2228_ = v___x_2215_;
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2226_);
                        crate::leanh::lean_dec(v___x_2215_);
                        v___x_2228_ = crate::leanh::lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2233_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2220_ = 0;
                v___x_2221_ = l_Lean_SourceInfo_fromRef(v_a_2216_, v___x_2220_);
                crate::leanh::lean_dec(v_a_2216_);
                if v_isShared_2219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2218_, 0, v___x_2221_);
                    v___x_2223_ = v___x_2218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2224_, 0, v___x_2221_);
                    v___x_2223_ = v_reuseFailAlloc_2224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2223_;
            }
            3 => {
                if v_isShared_2229_ == 0 {
                    v___x_2231_ = v___x_2228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
                    v___x_2231_ = v_reuseFailAlloc_2232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabMacro___lam__0___boxed(
    mut v___y_2234_: *mut crate::leanh::LeanObject,
    mut v___y_2235_: *mut crate::leanh::LeanObject,
    mut v___y_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2237_ = l_Lean_Elab_Command_elabMacro___lam__0(v___y_2234_, v___y_2235_);
    crate::leanh::lean_dec(v___y_2235_);
    crate::leanh::lean_dec_ref(v___y_2234_);
    return v_res_2237_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__3(
    mut v_env_2238_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2239_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2240_: *mut crate::leanh::LeanObject,
    mut v_n_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2244_ = l_Lean_ResolveName_resolveNamespace(
        v_env_2238_,
        v_currNamespace_2239_,
        v_openDecls_2240_,
        v_n_2241_,
    );
    v___x_2245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    crate::leanh::lean_ctor_set(v___x_2245_, 1, v___y_2243_);
    return v___x_2245_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__3___boxed(
    mut v_env_2246_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2247_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2248_: *mut crate::leanh::LeanObject,
    mut v_n_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__3(
            v_env_2246_,
            v_currNamespace_2247_,
            v_openDecls_2248_,
            v_n_2249_,
            v___y_2250_,
            v___y_2251_,
        );
    crate::leanh::lean_dec_ref(v___y_2250_);
    return v_res_2252_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__2(
    mut v_currNamespace_2253_: *mut crate::leanh::LeanObject,
    mut v___y_2254_: *mut crate::leanh::LeanObject,
    mut v___y_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2256_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2256_, 0, v_currNamespace_2253_);
    crate::leanh::lean_ctor_set(v___x_2256_, 1, v___y_2255_);
    return v___x_2256_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__2___boxed(
    mut v_currNamespace_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__2(
            v_currNamespace_2257_,
            v___y_2258_,
            v___y_2259_,
        );
    crate::leanh::lean_dec_ref(v___y_2258_);
    return v_res_2260_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2266_ = l_Lean_maxRecDepthErrorMessage;
    v___x_2267_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2267_, 0, v___x_2266_);
    return v___x_2267_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__3);
    v___x_2269_ = l_Lean_MessageData_ofFormat(v___x_2268_);
    return v___x_2269_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__4);
    v___x_2271_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__2;
    v___x_2272_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2272_, 0, v___x_2271_);
    crate::leanh::lean_ctor_set(v___x_2272_, 1, v___x_2270_);
    return v___x_2272_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg(
    mut v_ref_2273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___closed__5);
    v___x_2276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2276_, 0, v_ref_2273_);
    crate::leanh::lean_ctor_set(v___x_2276_, 1, v___x_2275_);
    v___x_2277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2277_, 0, v___x_2276_);
    return v___x_2277_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg___boxed(
    mut v_ref_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2280_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg(v_ref_2278_);
    return v_res_2280_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__0(
    mut v_env_2281_: *mut crate::leanh::LeanObject,
    mut v_declName_2282_: *mut crate::leanh::LeanObject,
    mut v___y_2283_: *mut crate::leanh::LeanObject,
    mut v___y_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: u8 = 0;
    let mut v_env_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: u8 = 0;
    let mut v___x_2289_: u8 = 0;
    v___x_2285_ = 0;
    v_env_2286_ = l_Lean_Environment_setExporting(v_env_2281_, v___x_2285_);
    crate::leanh::lean_inc(v_declName_2282_);
    v___x_2287_ = l_Lean_mkPrivateName(v_env_2286_, v_declName_2282_);
    v___x_2288_ = 1;
    crate::leanh::lean_inc_ref(v_env_2286_);
    v___x_2289_ = l_Lean_Environment_contains(v_env_2286_, v___x_2287_, v___x_2288_);
    if v___x_2289_ == 0 {
        let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2291_: u8 = 0;
        let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2290_ = l_Lean_privateToUserName(v_declName_2282_);
        v___x_2291_ = l_Lean_Environment_contains(v_env_2286_, v___x_2290_, v___x_2288_);
        v___x_2292_ = crate::leanh::lean_box((v___x_2291_) as usize);
        v___x_2293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2293_, 0, v___x_2292_);
        crate::leanh::lean_ctor_set(v___x_2293_, 1, v___y_2284_);
        return v___x_2293_;
    } else {
        let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_2286_);
        crate::leanh::lean_dec(v_declName_2282_);
        v___x_2294_ = crate::leanh::lean_box((v___x_2289_) as usize);
        v___x_2295_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2295_, 0, v___x_2294_);
        crate::leanh::lean_ctor_set(v___x_2295_, 1, v___y_2284_);
        return v___x_2295_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__0___boxed(
    mut v_env_2296_: *mut crate::leanh::LeanObject,
    mut v_declName_2297_: *mut crate::leanh::LeanObject,
    mut v___y_2298_: *mut crate::leanh::LeanObject,
    mut v___y_2299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2300_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__0(
            v_env_2296_,
            v_declName_2297_,
            v___y_2298_,
            v___y_2299_,
        );
    crate::leanh::lean_dec_ref(v___y_2298_);
    return v_res_2300_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__4(
    mut v_env_2301_: *mut crate::leanh::LeanObject,
    mut v_opts_2302_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2303_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2304_: *mut crate::leanh::LeanObject,
    mut v_n_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2308_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_2301_,
        v_opts_2302_,
        v_currNamespace_2303_,
        v_openDecls_2304_,
        v_n_2305_,
    );
    v___x_2309_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2309_, 0, v___x_2308_);
    crate::leanh::lean_ctor_set(v___x_2309_, 1, v___y_2307_);
    return v___x_2309_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__4___boxed(
    mut v_env_2310_: *mut crate::leanh::LeanObject,
    mut v_opts_2311_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2312_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2313_: *mut crate::leanh::LeanObject,
    mut v_n_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2317_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__4(
            v_env_2310_,
            v_opts_2311_,
            v_currNamespace_2312_,
            v_openDecls_2313_,
            v_n_2314_,
            v___y_2315_,
            v___y_2316_,
        );
    crate::leanh::lean_dec_ref(v___y_2315_);
    crate::leanh::lean_dec_ref(v_opts_2311_);
    return v_res_2317_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___redArg(
    mut v_x_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2318_) == 0 {
        let mut v_a_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2320_ = crate::leanh::lean_ctor_get(v_x_2318_, 0);
        crate::leanh::lean_inc(v_a_2320_);
        v___x_2321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2321_, 0, v_a_2320_);
        crate::leanh::lean_ctor_set(v___x_2321_, 1, v___y_2319_);
        return v___x_2321_;
    } else {
        let mut v_a_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2322_ = crate::leanh::lean_ctor_get(v_x_2318_, 0);
        crate::leanh::lean_inc(v_a_2322_);
        v___x_2323_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2323_, 0, v_a_2322_);
        crate::leanh::lean_ctor_set(v___x_2323_, 1, v___y_2319_);
        return v___x_2323_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___redArg___boxed(
    mut v_x_2324_: *mut crate::leanh::LeanObject,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2326_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___redArg(v_x_2324_, v___y_2325_);
    crate::leanh::lean_dec_ref(v_x_2324_);
    return v_res_2326_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__1(
    mut v_env_2327_: *mut crate::leanh::LeanObject,
    mut v_stx_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2336_: u8 = 0;
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2341_: u8 = 0;
    let mut v_unused_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2346_: u8 = 0;
    let mut v_snd_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2357_: u8 = 0;
    let mut v_a_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2331_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_2327_,
                    v_stx_2328_,
                    v___y_2329_,
                    v___y_2330_,
                );
                if crate::leanh::lean_obj_tag(v___x_2331_) == 0 {
                    v_a_2332_ = crate::leanh::lean_ctor_get(v___x_2331_, 0);
                    crate::leanh::lean_inc(v_a_2332_);
                    if crate::leanh::lean_obj_tag(v_a_2332_) == 0 {
                        v_a_2333_ = crate::leanh::lean_ctor_get(v___x_2331_, 1);
                        v_isSharedCheck_2341_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2331_)) as u8;
                        if v_isSharedCheck_2341_ == 0 {
                            v_unused_2342_ = crate::leanh::lean_ctor_get(v___x_2331_, 0);
                            crate::leanh::lean_dec(v_unused_2342_);
                            v___x_2335_ = v___x_2331_;
                            v_isShared_2336_ = v_isSharedCheck_2341_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2333_);
                            crate::leanh::lean_dec(v___x_2331_);
                            v___x_2335_ = crate::leanh::lean_box(0);
                            v_isShared_2336_ = v_isSharedCheck_2341_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_2343_ = crate::leanh::lean_ctor_get(v_a_2332_, 0);
                        v_isSharedCheck_2371_ = (!crate::leanh::lean_is_exclusive(v_a_2332_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v___x_2345_ = v_a_2332_;
                            v_isShared_2346_ = v_isSharedCheck_2371_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2343_);
                            crate::leanh::lean_dec(v_a_2332_);
                            v___x_2345_ = crate::leanh::lean_box(0);
                            v_isShared_2346_ = v_isSharedCheck_2371_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2331_, 0);
                    v_a_2373_ = crate::leanh::lean_ctor_get(v___x_2331_, 1);
                    v_isSharedCheck_2380_ = (!crate::leanh::lean_is_exclusive(v___x_2331_)) as u8;
                    if v_isSharedCheck_2380_ == 0 {
                        v___x_2375_ = v___x_2331_;
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2373_);
                        crate::leanh::lean_inc(v_a_2372_);
                        crate::leanh::lean_dec(v___x_2331_);
                        v___x_2375_ = crate::leanh::lean_box(0);
                        v_isShared_2376_ = v_isSharedCheck_2380_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2337_ = crate::leanh::lean_box(0);
                if v_isShared_2336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2335_, 0, v___x_2337_);
                    v___x_2339_ = v___x_2335_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2340_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2340_, 1, v_a_2333_);
                    v___x_2339_ = v_reuseFailAlloc_2340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2339_;
            }
            3 => {
                v_snd_2347_ = crate::leanh::lean_ctor_get(v_val_2343_, 1);
                crate::leanh::lean_inc(v_snd_2347_);
                crate::leanh::lean_dec(v_val_2343_);
                if crate::leanh::lean_obj_tag(v_snd_2347_) == 0 {
                    crate::leanh::lean_del_object(v___x_2345_);
                    v_a_2348_ = crate::leanh::lean_ctor_get(v___x_2331_, 1);
                    crate::leanh::lean_inc(v_a_2348_);
                    crate::leanh::lean_dec_ref_known(v___x_2331_, 2);
                    v_a_2349_ = crate::leanh::lean_ctor_get(v_snd_2347_, 0);
                    v_isSharedCheck_2357_ = (!crate::leanh::lean_is_exclusive(v_snd_2347_)) as u8;
                    if v_isSharedCheck_2357_ == 0 {
                        v___x_2351_ = v_snd_2347_;
                        v_isShared_2352_ = v_isSharedCheck_2357_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2349_);
                        crate::leanh::lean_dec(v_snd_2347_);
                        v___x_2351_ = crate::leanh::lean_box(0);
                        v_isShared_2352_ = v_isSharedCheck_2357_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2358_ = crate::leanh::lean_ctor_get(v___x_2331_, 1);
                    crate::leanh::lean_inc(v_a_2358_);
                    crate::leanh::lean_dec_ref_known(v___x_2331_, 2);
                    v_a_2359_ = crate::leanh::lean_ctor_get(v_snd_2347_, 0);
                    v_isSharedCheck_2370_ = (!crate::leanh::lean_is_exclusive(v_snd_2347_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2361_ = v_snd_2347_;
                        v_isShared_2362_ = v_isSharedCheck_2370_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2359_);
                        crate::leanh::lean_dec(v_snd_2347_);
                        v___x_2361_ = crate::leanh::lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2370_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2352_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2356_, 0, v_a_2349_);
                    v___x_2354_ = v_reuseFailAlloc_2356_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2355_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___redArg(v___x_2354_, v_a_2348_);
                crate::leanh::lean_dec_ref(v___x_2354_);
                return v___x_2355_;
            }
            6 => {
                if v_isShared_2346_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2345_, 0, v_a_2359_);
                    v___x_2364_ = v___x_2345_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2359_);
                    v___x_2364_ = v_reuseFailAlloc_2369_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2361_, 0, v___x_2364_);
                    v___x_2366_ = v___x_2361_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2368_, 0, v___x_2364_);
                    v___x_2366_ = v_reuseFailAlloc_2368_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2367_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___redArg(v___x_2366_, v_a_2358_);
                crate::leanh::lean_dec_ref(v___x_2366_);
                return v___x_2367_;
            }
            9 => {
                if v_isShared_2376_ == 0 {
                    v___x_2378_ = v___x_2375_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2372_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_a_2373_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__1___boxed(
    mut v_env_2381_: *mut crate::leanh::LeanObject,
    mut v_stx_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__1(
            v_env_2381_,
            v_stx_2382_,
            v___y_2383_,
            v___y_2384_,
        );
    crate::leanh::lean_dec_ref(v___y_2383_);
    return v_res_2385_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13___redArg(
    mut v_a_2386_: *mut crate::leanh::LeanObject,
    mut v_x_2387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: u8 = 0;
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2387_) == 0 {
                    v___x_2388_ = crate::leanh::lean_box(0);
                    return v___x_2388_;
                } else {
                    v_key_2389_ = crate::leanh::lean_ctor_get(v_x_2387_, 0);
                    v_value_2390_ = crate::leanh::lean_ctor_get(v_x_2387_, 1);
                    v_tail_2391_ = crate::leanh::lean_ctor_get(v_x_2387_, 2);
                    v___x_2392_ = lean_name_eq(v_key_2389_, v_a_2386_);
                    if v___x_2392_ == 0 {
                        v_x_2387_ = v_tail_2391_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2390_);
                        v___x_2394_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2394_, 0, v_value_2390_);
                        return v___x_2394_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13___redArg___boxed(
    mut v_a_2395_: *mut crate::leanh::LeanObject,
    mut v_x_2396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2397_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13___redArg(v_a_2395_, v_x_2396_);
    crate::leanh::lean_dec(v_x_2396_);
    crate::leanh::lean_dec(v_a_2395_);
    return v_res_2397_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___closed__0()
-> u64 {
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: u64 = 0;
    v___x_2398_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2399_ = lean_uint64_of_nat(v___x_2398_);
    return v___x_2399_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg(
    mut v_m_2400_: *mut crate::leanh::LeanObject,
    mut v_a_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2405_: u64 = 0;
    let mut v___x_2406_: u64 = 0;
    let mut v___x_2407_: u64 = 0;
    let mut v_fold_2408_: u64 = 0;
    let mut v___x_2409_: u64 = 0;
    let mut v___x_2410_: u64 = 0;
    let mut v___x_2411_: u64 = 0;
    let mut v___x_2412_: usize = 0;
    let mut v___x_2413_: usize = 0;
    let mut v___x_2414_: usize = 0;
    let mut v___x_2415_: usize = 0;
    let mut v___x_2416_: usize = 0;
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: u64 = 0;
    let mut v_hash_2420_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2402_ = crate::leanh::lean_ctor_get(v_m_2400_, 1);
                v___x_2403_ = lean_array_get_size(v_buckets_2402_);
                if crate::leanh::lean_obj_tag(v_a_2401_) == 0 {
                    v___x_2419_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___closed__0);
                    v___y_2405_ = v___x_2419_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2420_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2401_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2405_ = v_hash_2420_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2406_ = 32u64;
                v___x_2407_ = lean_uint64_shift_right(v___y_2405_, v___x_2406_);
                v_fold_2408_ = lean_uint64_xor(v___y_2405_, v___x_2407_);
                v___x_2409_ = 16u64;
                v___x_2410_ = lean_uint64_shift_right(v_fold_2408_, v___x_2409_);
                v___x_2411_ = lean_uint64_xor(v_fold_2408_, v___x_2410_);
                v___x_2412_ = lean_uint64_to_usize(v___x_2411_);
                v___x_2413_ = lean_usize_of_nat(v___x_2403_);
                v___x_2414_ = 1usize;
                v___x_2415_ = lean_usize_sub(v___x_2413_, v___x_2414_);
                v___x_2416_ = lean_usize_land(v___x_2412_, v___x_2415_);
                v___x_2417_ = lean_array_uget_borrowed(v_buckets_2402_, v___x_2416_);
                v___x_2418_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13___redArg(v_a_2401_, v___x_2417_);
                return v___x_2418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_m_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg(v_m_2421_, v_a_2422_);
    crate::leanh::lean_dec(v_a_2422_);
    crate::leanh::lean_dec_ref(v_m_2421_);
    return v_res_2423_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(
    mut v_keys_2424_: *mut crate::leanh::LeanObject,
    mut v_i_2425_: *mut crate::leanh::LeanObject,
    mut v_k_2426_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: u8 = 0;
    let mut v_k_x27_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2427_ = lean_array_get_size(v_keys_2424_);
                v___x_2428_ = lean_nat_dec_lt(v_i_2425_, v___x_2427_);
                if v___x_2428_ == 0 {
                    crate::leanh::lean_dec(v_i_2425_);
                    return v___x_2428_;
                } else {
                    v_k_x27_2429_ = lean_array_fget_borrowed(v_keys_2424_, v_i_2425_);
                    v___x_2430_ = l_Lean_instBEqExtraModUse_beq(v_k_2426_, v_k_x27_2429_);
                    if v___x_2430_ == 0 {
                        v___x_2431_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2432_ = lean_nat_add(v_i_2425_, v___x_2431_);
                        crate::leanh::lean_dec(v_i_2425_);
                        v_i_2425_ = v___x_2432_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2425_);
                        return v___x_2430_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg___boxed(
    mut v_keys_2434_: *mut crate::leanh::LeanObject,
    mut v_i_2435_: *mut crate::leanh::LeanObject,
    mut v_k_2436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2437_: u8 = 0;
    let mut v_r_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2437_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(v_keys_2434_, v_i_2435_, v_k_2436_);
    crate::leanh::lean_dec_ref(v_k_2436_);
    crate::leanh::lean_dec_ref(v_keys_2434_);
    v_r_2438_ = crate::leanh::lean_box((v_res_2437_) as usize);
    return v_r_2438_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0()
-> usize {
    let mut v___x_2439_: usize = 0;
    let mut v___x_2440_: usize = 0;
    let mut v___x_2441_: usize = 0;
    v___x_2439_ = 5usize;
    v___x_2440_ = 1usize;
    v___x_2441_ = lean_usize_shift_left(v___x_2440_, v___x_2439_);
    return v___x_2441_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1()
-> usize {
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    v___x_2442_ = 1usize;
    v___x_2443_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__0);
    v___x_2444_ = lean_usize_sub(v___x_2443_, v___x_2442_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(
    mut v_x_2445_: *mut crate::leanh::LeanObject,
    mut v_x_2446_: usize,
    mut v_x_2447_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v___x_2452_: usize = 0;
    let mut v_j_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: u8 = 0;
    let mut v_node_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: usize = 0;
    let mut v___x_2460_: u8 = 0;
    let mut v_ks_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2445_) == 0 {
                    v_es_2448_ = crate::leanh::lean_ctor_get(v_x_2445_, 0);
                    v___x_2449_ = crate::leanh::lean_box(2);
                    v___x_2450_ = 5usize;
                    v___x_2451_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___closed__1);
                    v___x_2452_ = lean_usize_land(v_x_2446_, v___x_2451_);
                    v_j_2453_ = lean_usize_to_nat(v___x_2452_);
                    v___x_2454_ = lean_array_get_borrowed(v___x_2449_, v_es_2448_, v_j_2453_);
                    crate::leanh::lean_dec(v_j_2453_);
                    match crate::leanh::lean_obj_tag(v___x_2454_) {
                        0 => {
                            v_key_2455_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                            v___x_2456_ = l_Lean_instBEqExtraModUse_beq(v_x_2447_, v_key_2455_);
                            return v___x_2456_;
                        }
                        1 => {
                            v_node_2457_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                            v___x_2458_ = lean_usize_shift_right(v_x_2446_, v___x_2450_);
                            v_x_2445_ = v_node_2457_;
                            v_x_2446_ = v___x_2458_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2460_ = 0;
                            return v___x_2460_;
                        }
                    }
                } else {
                    v_ks_2461_ = crate::leanh::lean_ctor_get(v_x_2445_, 0);
                    v___x_2462_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2463_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(v_ks_2461_, v___x_2462_, v_x_2447_);
                    return v___x_2463_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg___boxed(
    mut v_x_2464_: *mut crate::leanh::LeanObject,
    mut v_x_2465_: *mut crate::leanh::LeanObject,
    mut v_x_2466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_30229__boxed_2467_: usize = 0;
    let mut v_res_2468_: u8 = 0;
    let mut v_r_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_30229__boxed_2467_ = crate::leanh::lean_unbox_usize(v_x_2465_);
    crate::leanh::lean_dec(v_x_2465_);
    v_res_2468_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(v_x_2464_, v_x_30229__boxed_2467_, v_x_2466_);
    crate::leanh::lean_dec_ref(v_x_2466_);
    crate::leanh::lean_dec_ref(v_x_2464_);
    v_r_2469_ = crate::leanh::lean_box((v_res_2468_) as usize);
    return v_r_2469_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10___redArg(
    mut v_x_2470_: *mut crate::leanh::LeanObject,
    mut v_x_2471_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2472_: u64 = 0;
    let mut v___x_2473_: usize = 0;
    let mut v___x_2474_: u8 = 0;
    v___x_2472_ = l_Lean_instHashableExtraModUse_hash(v_x_2471_);
    v___x_2473_ = lean_uint64_to_usize(v___x_2472_);
    v___x_2474_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(v_x_2470_, v___x_2473_, v_x_2471_);
    return v___x_2474_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10___redArg___boxed(
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v_x_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2477_: u8 = 0;
    let mut v_r_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2477_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10___redArg(v_x_2475_, v_x_2476_);
    crate::leanh::lean_dec_ref(v_x_2476_);
    crate::leanh::lean_dec_ref(v_x_2475_);
    v_r_2478_ = crate::leanh::lean_box((v_res_2477_) as usize);
    return v_r_2478_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2479_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2480_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_2481_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2481_, 0, v___x_2480_);
    return v___x_2481_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2482_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_2483_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2484_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2484_, 0, v___x_2483_);
    crate::leanh::lean_ctor_set(v___x_2484_, 1, v___x_2483_);
    crate::leanh::lean_ctor_set(v___x_2484_, 2, v___x_2483_);
    crate::leanh::lean_ctor_set(v___x_2484_, 3, v___x_2483_);
    crate::leanh::lean_ctor_set(v___x_2484_, 4, v___x_2482_);
    crate::leanh::lean_ctor_set(v___x_2484_, 5, v___x_2482_);
    crate::leanh::lean_ctor_set(v___x_2484_, 6, v___x_2482_);
    crate::leanh::lean_ctor_set(v___x_2484_, 7, v___x_2482_);
    crate::leanh::lean_ctor_set(v___x_2484_, 8, v___x_2482_);
    crate::leanh::lean_ctor_set(v___x_2484_, 9, v___x_2482_);
    return v___x_2484_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2486_ = lean_mk_empty_array_with_capacity(v___x_2485_);
    v___x_2487_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2487_, 0, v___x_2486_);
    return v___x_2487_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2488_: usize = 0;
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2488_ = 5usize;
    v___x_2489_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2490_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2491_ = lean_mk_empty_array_with_capacity(v___x_2490_);
    v___x_2492_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__3);
    v___x_2493_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    crate::leanh::lean_ctor_set(v___x_2493_, 1, v___x_2491_);
    crate::leanh::lean_ctor_set(v___x_2493_, 2, v___x_2489_);
    crate::leanh::lean_ctor_set(v___x_2493_, 3, v___x_2489_);
    crate::leanh::lean_ctor_set_usize(v___x_2493_, 4, v___x_2488_);
    return v___x_2493_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2494_ = crate::leanh::lean_box(1);
    v___x_2495_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__4);
    v___x_2496_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_2497_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2497_, 0, v___x_2496_);
    crate::leanh::lean_ctor_set(v___x_2497_, 1, v___x_2495_);
    crate::leanh::lean_ctor_set(v___x_2497_, 2, v___x_2494_);
    return v___x_2497_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2501_ = lean_st_ref_get(v___y_2499_);
    v_env_2502_ = crate::leanh::lean_ctor_get(v___x_2501_, 0);
    crate::leanh::lean_inc_ref(v_env_2502_);
    crate::leanh::lean_dec(v___x_2501_);
    v___x_2503_ = lean_st_ref_get(v___y_2499_);
    v_scopes_2504_ = crate::leanh::lean_ctor_get(v___x_2503_, 2);
    crate::leanh::lean_inc(v_scopes_2504_);
    crate::leanh::lean_dec(v___x_2503_);
    v___x_2505_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_2506_ = l_List_head_x21___redArg(v___x_2505_, v_scopes_2504_);
    crate::leanh::lean_dec(v_scopes_2504_);
    v_opts_2507_ = crate::leanh::lean_ctor_get(v___x_2506_, 1);
    crate::leanh::lean_inc_ref(v_opts_2507_);
    crate::leanh::lean_dec(v___x_2506_);
    v___x_2508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__2);
    v___x_2509_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___closed__5);
    v___x_2510_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2510_, 0, v_env_2502_);
    crate::leanh::lean_ctor_set(v___x_2510_, 1, v___x_2508_);
    crate::leanh::lean_ctor_set(v___x_2510_, 2, v___x_2509_);
    crate::leanh::lean_ctor_set(v___x_2510_, 3, v_opts_2507_);
    v___x_2511_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2511_, 0, v___x_2510_);
    crate::leanh::lean_ctor_set(v___x_2511_, 1, v_msgData_2498_);
    v___x_2512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2512_, 0, v___x_2511_);
    return v___x_2512_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2516_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg(v_msgData_2513_, v___y_2514_);
    crate::leanh::lean_dec(v___y_2514_);
    return v_res_2516_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__0()
-> f64 {
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: f64 = 0.0;
    v___x_2517_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2518_ = lean_float_of_nat(v___x_2517_);
    return v___x_2518_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1(
    mut v_cls_2522_: *mut crate::leanh::LeanObject,
    mut v_msg_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2533_: u8 = 0;
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2548_: u8 = 0;
    let mut v_tid_2549_: u64 = 0;
    let mut v_traces_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2553_: u8 = 0;
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: f64 = 0.0;
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2574_: u8 = 0;
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_isSharedCheck_2576_: u8 = 0;
    let mut v_a_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2527_ = l_Lean_Elab_Command_getRef___redArg(v___y_2524_);
                if crate::leanh::lean_obj_tag(v___x_2527_) == 0 {
                    v_a_2528_ = crate::leanh::lean_ctor_get(v___x_2527_, 0);
                    crate::leanh::lean_inc(v_a_2528_);
                    crate::leanh::lean_dec_ref_known(v___x_2527_, 1);
                    v___x_2529_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg(v_msg_2523_, v___y_2525_);
                    v_a_2530_ = crate::leanh::lean_ctor_get(v___x_2529_, 0);
                    v_isSharedCheck_2576_ = (!crate::leanh::lean_is_exclusive(v___x_2529_)) as u8;
                    if v_isSharedCheck_2576_ == 0 {
                        v___x_2532_ = v___x_2529_;
                        v_isShared_2533_ = v_isSharedCheck_2576_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2530_);
                        crate::leanh::lean_dec(v___x_2529_);
                        v___x_2532_ = crate::leanh::lean_box(0);
                        v_isShared_2533_ = v_isSharedCheck_2576_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2523_);
                    crate::leanh::lean_dec(v_cls_2522_);
                    v_a_2577_ = crate::leanh::lean_ctor_get(v___x_2527_, 0);
                    v_isSharedCheck_2584_ = (!crate::leanh::lean_is_exclusive(v___x_2527_)) as u8;
                    if v_isSharedCheck_2584_ == 0 {
                        v___x_2579_ = v___x_2527_;
                        v_isShared_2580_ = v_isSharedCheck_2584_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2577_);
                        crate::leanh::lean_dec(v___x_2527_);
                        v___x_2579_ = crate::leanh::lean_box(0);
                        v_isShared_2580_ = v_isSharedCheck_2584_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2534_ = lean_st_ref_take(v___y_2525_);
                v_traceState_2535_ = crate::leanh::lean_ctor_get(v___x_2534_, 9);
                v_env_2536_ = crate::leanh::lean_ctor_get(v___x_2534_, 0);
                v_messages_2537_ = crate::leanh::lean_ctor_get(v___x_2534_, 1);
                v_scopes_2538_ = crate::leanh::lean_ctor_get(v___x_2534_, 2);
                v_usedQuotCtxts_2539_ = crate::leanh::lean_ctor_get(v___x_2534_, 3);
                v_nextMacroScope_2540_ = crate::leanh::lean_ctor_get(v___x_2534_, 4);
                v_maxRecDepth_2541_ = crate::leanh::lean_ctor_get(v___x_2534_, 5);
                v_ngen_2542_ = crate::leanh::lean_ctor_get(v___x_2534_, 6);
                v_auxDeclNGen_2543_ = crate::leanh::lean_ctor_get(v___x_2534_, 7);
                v_infoState_2544_ = crate::leanh::lean_ctor_get(v___x_2534_, 8);
                v_snapshotTasks_2545_ = crate::leanh::lean_ctor_get(v___x_2534_, 10);
                v_isSharedCheck_2575_ = (!crate::leanh::lean_is_exclusive(v___x_2534_)) as u8;
                if v_isSharedCheck_2575_ == 0 {
                    v___x_2547_ = v___x_2534_;
                    v_isShared_2548_ = v_isSharedCheck_2575_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2545_);
                    crate::leanh::lean_inc(v_traceState_2535_);
                    crate::leanh::lean_inc(v_infoState_2544_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2543_);
                    crate::leanh::lean_inc(v_ngen_2542_);
                    crate::leanh::lean_inc(v_maxRecDepth_2541_);
                    crate::leanh::lean_inc(v_nextMacroScope_2540_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2539_);
                    crate::leanh::lean_inc(v_scopes_2538_);
                    crate::leanh::lean_inc(v_messages_2537_);
                    crate::leanh::lean_inc(v_env_2536_);
                    crate::leanh::lean_dec(v___x_2534_);
                    v___x_2547_ = crate::leanh::lean_box(0);
                    v_isShared_2548_ = v_isSharedCheck_2575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2549_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2535_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2550_ = crate::leanh::lean_ctor_get(v_traceState_2535_, 0);
                v_isSharedCheck_2574_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2535_)) as u8;
                if v_isSharedCheck_2574_ == 0 {
                    v___x_2552_ = v_traceState_2535_;
                    v_isShared_2553_ = v_isSharedCheck_2574_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2550_);
                    crate::leanh::lean_dec(v_traceState_2535_);
                    v___x_2552_ = crate::leanh::lean_box(0);
                    v_isShared_2553_ = v_isSharedCheck_2574_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2554_ = crate::leanh::lean_box(0);
                v___x_2555_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__0);
                v___x_2556_ = 0;
                v___x_2557_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__1;
                v___x_2558_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2558_, 0, v_cls_2522_);
                crate::leanh::lean_ctor_set(v___x_2558_, 1, v___x_2554_);
                crate::leanh::lean_ctor_set(v___x_2558_, 2, v___x_2557_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2555_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2555_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2558_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2556_,
                );
                v___x_2559_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__2;
                v___x_2560_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2560_, 0, v___x_2558_);
                crate::leanh::lean_ctor_set(v___x_2560_, 1, v_a_2530_);
                crate::leanh::lean_ctor_set(v___x_2560_, 2, v___x_2559_);
                v___x_2561_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2561_, 0, v_a_2528_);
                crate::leanh::lean_ctor_set(v___x_2561_, 1, v___x_2560_);
                v___x_2562_ = l_Lean_PersistentArray_push___redArg(v_traces_2550_, v___x_2561_);
                if v_isShared_2553_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2562_);
                    v___x_2564_ = v___x_2552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2573_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2562_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2573_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2549_,
                    );
                    v___x_2564_ = v_reuseFailAlloc_2573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2548_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2547_, 9, v___x_2564_);
                    v___x_2566_ = v___x_2547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2572_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_env_2536_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 1, v_messages_2537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 2, v_scopes_2538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 3, v_usedQuotCtxts_2539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 4, v_nextMacroScope_2540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 5, v_maxRecDepth_2541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 6, v_ngen_2542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 7, v_auxDeclNGen_2543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 8, v_infoState_2544_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 9, v___x_2564_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2572_, 10, v_snapshotTasks_2545_);
                    v___x_2566_ = v_reuseFailAlloc_2572_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2567_ = lean_st_ref_set(v___y_2525_, v___x_2566_);
                v___x_2568_ = crate::leanh::lean_box(0);
                if v_isShared_2533_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2568_);
                    v___x_2570_ = v___x_2532_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2571_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
                    v___x_2570_ = v_reuseFailAlloc_2571_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2570_;
            }
            7 => {
                if v_isShared_2580_ == 0 {
                    v___x_2582_ = v___x_2579_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
                    v___x_2582_ = v_reuseFailAlloc_2583_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___boxed(
    mut v_cls_2585_: *mut crate::leanh::LeanObject,
    mut v_msg_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
    mut v___y_2588_: *mut crate::leanh::LeanObject,
    mut v___y_2589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2590_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1(v_cls_2585_, v_msg_2586_, v___y_2587_, v___y_2588_);
    crate::leanh::lean_dec(v___y_2588_);
    crate::leanh::lean_dec_ref(v___y_2587_);
    return v_res_2590_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2593_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__1;
    v___x_2594_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__0;
    v___x_2595_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2594_,
        v___x_2593_,
    );
    return v___x_2595_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2600_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__5;
    v___x_2601_ = l_Lean_stringToMessageData(v___x_2600_);
    return v___x_2601_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2603_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__7;
    v___x_2604_ = l_Lean_stringToMessageData(v___x_2603_);
    return v___x_2604_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2605_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__1;
    v___x_2606_ = l_Lean_stringToMessageData(v___x_2605_);
    return v___x_2606_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_2610_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__4;
    v___x_2611_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__11;
    v___x_2612_ = l_Lean_Name_append(v___x_2611_, v_cls_2610_);
    return v___x_2612_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2614_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__13;
    v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
    return v___x_2615_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2617_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__15;
    v___x_2618_ = l_Lean_stringToMessageData(v___x_2617_);
    return v___x_2618_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6(
    mut v_mod_2623_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2624_: u8,
    mut v_hint_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2631_: u8 = 0;
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2656_: u8 = 0;
    let mut v_asyncMode_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: u8 = 0;
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2675_: u8 = 0;
    let mut v_cls_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: u8 = 0;
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2629_ = lean_st_ref_get(v___y_2627_);
                v_env_2630_ = crate::leanh::lean_ctor_get(v___x_2629_, 0);
                crate::leanh::lean_inc_ref(v_env_2630_);
                crate::leanh::lean_dec(v___x_2629_);
                v_isExporting_2631_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2630_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_2630_);
                v___x_2632_ = lean_st_ref_get(v___y_2627_);
                v_env_2633_ = crate::leanh::lean_ctor_get(v___x_2632_, 0);
                crate::leanh::lean_inc_ref(v_env_2633_);
                crate::leanh::lean_dec(v___x_2632_);
                v___x_2634_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__2);
                crate::leanh::lean_inc(v_mod_2623_);
                v_entry_2635_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_2635_, 0, v_mod_2623_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_2635_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_2631_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_2635_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_2624_,
                );
                v___x_2636_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_2637_ = crate::leanh::lean_box(1);
                v___x_2638_ = crate::leanh::lean_box(0);
                v___x_2666_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2634_,
                    v___x_2636_,
                    v_env_2633_,
                    v___x_2637_,
                    v___x_2638_,
                );
                v___x_2667_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10___redArg(v___x_2666_, v_entry_2635_);
                crate::leanh::lean_dec(v___x_2666_);
                if v___x_2667_ == 0 {
                    v___x_2668_ = l_Lean_inheritedTraceOptions;
                    v___x_2669_ = lean_st_ref_get(v___x_2668_);
                    v___x_2670_ = lean_st_ref_get(v___y_2627_);
                    v_scopes_2671_ = crate::leanh::lean_ctor_get(v___x_2670_, 2);
                    crate::leanh::lean_inc(v_scopes_2671_);
                    crate::leanh::lean_dec(v___x_2670_);
                    v___x_2672_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2673_ = l_List_head_x21___redArg(v___x_2672_, v_scopes_2671_);
                    crate::leanh::lean_dec(v_scopes_2671_);
                    v_opts_2674_ = crate::leanh::lean_ctor_get(v___x_2673_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2674_);
                    crate::leanh::lean_dec(v___x_2673_);
                    v_hasTrace_2675_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_2674_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2675_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_2674_);
                        crate::leanh::lean_dec(v___x_2669_);
                        crate::leanh::lean_dec(v_hint_2625_);
                        crate::leanh::lean_dec(v_mod_2623_);
                        v___y_2640_ = v___y_2627_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_2676_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__4;
                        v___x_2696_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__12);
                        v___x_2697_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_2669_,
                            v_opts_2674_,
                            v___x_2696_,
                        );
                        crate::leanh::lean_dec_ref(v_opts_2674_);
                        crate::leanh::lean_dec(v___x_2669_);
                        if v___x_2697_ == 0 {
                            crate::leanh::lean_dec(v_hint_2625_);
                            crate::leanh::lean_dec(v_mod_2623_);
                            v___y_2640_ = v___y_2627_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2698_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__14);
                            if v_isExporting_2631_ == 0 {
                                v___x_2707_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__19;
                                v___y_2700_ = v___x_2707_;
                                state = 6;
                                continue;
                            } else {
                                v___x_2708_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__20;
                                v___y_2700_ = v___x_2708_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_2635_, 1);
                    crate::leanh::lean_dec(v_hint_2625_);
                    crate::leanh::lean_dec(v_mod_2623_);
                    v___x_2709_ = crate::leanh::lean_box(0);
                    v___x_2710_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2710_, 0, v___x_2709_);
                    return v___x_2710_;
                }
            }
            1 => {
                v___x_2641_ = lean_st_ref_take(v___y_2640_);
                v_toEnvExtension_2642_ = crate::leanh::lean_ctor_get(v___x_2636_, 0);
                v_env_2643_ = crate::leanh::lean_ctor_get(v___x_2641_, 0);
                v_messages_2644_ = crate::leanh::lean_ctor_get(v___x_2641_, 1);
                v_scopes_2645_ = crate::leanh::lean_ctor_get(v___x_2641_, 2);
                v_usedQuotCtxts_2646_ = crate::leanh::lean_ctor_get(v___x_2641_, 3);
                v_nextMacroScope_2647_ = crate::leanh::lean_ctor_get(v___x_2641_, 4);
                v_maxRecDepth_2648_ = crate::leanh::lean_ctor_get(v___x_2641_, 5);
                v_ngen_2649_ = crate::leanh::lean_ctor_get(v___x_2641_, 6);
                v_auxDeclNGen_2650_ = crate::leanh::lean_ctor_get(v___x_2641_, 7);
                v_infoState_2651_ = crate::leanh::lean_ctor_get(v___x_2641_, 8);
                v_traceState_2652_ = crate::leanh::lean_ctor_get(v___x_2641_, 9);
                v_snapshotTasks_2653_ = crate::leanh::lean_ctor_get(v___x_2641_, 10);
                v_isSharedCheck_2665_ = (!crate::leanh::lean_is_exclusive(v___x_2641_)) as u8;
                if v_isSharedCheck_2665_ == 0 {
                    v___x_2655_ = v___x_2641_;
                    v_isShared_2656_ = v_isSharedCheck_2665_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2653_);
                    crate::leanh::lean_inc(v_traceState_2652_);
                    crate::leanh::lean_inc(v_infoState_2651_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2650_);
                    crate::leanh::lean_inc(v_ngen_2649_);
                    crate::leanh::lean_inc(v_maxRecDepth_2648_);
                    crate::leanh::lean_inc(v_nextMacroScope_2647_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_2646_);
                    crate::leanh::lean_inc(v_scopes_2645_);
                    crate::leanh::lean_inc(v_messages_2644_);
                    crate::leanh::lean_inc(v_env_2643_);
                    crate::leanh::lean_dec(v___x_2641_);
                    v___x_2655_ = crate::leanh::lean_box(0);
                    v_isShared_2656_ = v_isSharedCheck_2665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_2657_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2642_, 2);
                v___x_2658_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2636_,
                    v_env_2643_,
                    v_entry_2635_,
                    v_asyncMode_2657_,
                    v___x_2638_,
                );
                if v_isShared_2656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2655_, 0, v___x_2658_);
                    v___x_2660_ = v___x_2655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2664_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_messages_2644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 2, v_scopes_2645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 3, v_usedQuotCtxts_2646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 4, v_nextMacroScope_2647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 5, v_maxRecDepth_2648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 6, v_ngen_2649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 7, v_auxDeclNGen_2650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 8, v_infoState_2651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 9, v_traceState_2652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 10, v_snapshotTasks_2653_);
                    v___x_2660_ = v_reuseFailAlloc_2664_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2661_ = lean_st_ref_set(v___y_2640_, v___x_2660_);
                v___x_2662_ = crate::leanh::lean_box(0);
                v___x_2663_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2663_, 0, v___x_2662_);
                return v___x_2663_;
            }
            4 => {
                v___x_2680_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2680_, 0, v___y_2678_);
                crate::leanh::lean_ctor_set(v___x_2680_, 1, v___y_2679_);
                v___x_2681_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1(v_cls_2676_, v___x_2680_, v___y_2626_, v___y_2627_);
                if crate::leanh::lean_obj_tag(v___x_2681_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2681_, 1);
                    v___y_2640_ = v___y_2627_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_2635_, 1);
                    return v___x_2681_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_2684_);
                v___x_2685_ = l_Lean_stringToMessageData(v___y_2684_);
                v___x_2686_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2686_, 0, v___y_2683_);
                crate::leanh::lean_ctor_set(v___x_2686_, 1, v___x_2685_);
                v___x_2687_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__6);
                v___x_2688_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2688_, 0, v___x_2686_);
                crate::leanh::lean_ctor_set(v___x_2688_, 1, v___x_2687_);
                v___x_2689_ = l_Lean_MessageData_ofName(v_mod_2623_);
                v___x_2690_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2690_, 0, v___x_2688_);
                crate::leanh::lean_ctor_set(v___x_2690_, 1, v___x_2689_);
                v___x_2691_ = l_Lean_Name_isAnonymous(v_hint_2625_);
                if v___x_2691_ == 0 {
                    v___x_2692_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__8);
                    v___x_2693_ = l_Lean_MessageData_ofName(v_hint_2625_);
                    v___x_2694_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2694_, 0, v___x_2692_);
                    crate::leanh::lean_ctor_set(v___x_2694_, 1, v___x_2693_);
                    v___y_2678_ = v___x_2690_;
                    v___y_2679_ = v___x_2694_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_2625_);
                    v___x_2695_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__9);
                    v___y_2678_ = v___x_2690_;
                    v___y_2679_ = v___x_2695_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_2700_);
                v___x_2701_ = l_Lean_stringToMessageData(v___y_2700_);
                v___x_2702_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2702_, 0, v___x_2698_);
                crate::leanh::lean_ctor_set(v___x_2702_, 1, v___x_2701_);
                v___x_2703_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__16);
                v___x_2704_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2702_);
                crate::leanh::lean_ctor_set(v___x_2704_, 1, v___x_2703_);
                if v_isMeta_2624_ == 0 {
                    v___x_2705_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__17;
                    v___y_2683_ = v___x_2704_;
                    v___y_2684_ = v___x_2705_;
                    state = 5;
                    continue;
                } else {
                    v___x_2706_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__18;
                    v___y_2683_ = v___x_2704_;
                    v___y_2684_ = v___x_2706_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___boxed(
    mut v_mod_2711_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2712_: *mut crate::leanh::LeanObject,
    mut v_hint_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_2717_: u8 = 0;
    let mut v_res_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2717_ = (crate::leanh::lean_unbox(v_isMeta_2712_) as u8);
    v_res_2718_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6(v_mod_2711_, v_isMeta_boxed_2717_, v_hint_2713_, v___y_2714_, v___y_2715_);
    crate::leanh::lean_dec(v___y_2715_);
    crate::leanh::lean_dec_ref(v___y_2714_);
    return v_res_2718_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__7(
    mut v___x_2719_: *mut crate::leanh::LeanObject,
    mut v_declName_2720_: *mut crate::leanh::LeanObject,
    mut v_as_2721_: *mut crate::leanh::LeanObject,
    mut v_sz_2722_: usize,
    mut v_i_2723_: usize,
    mut v_b_2724_: *mut crate::leanh::LeanObject,
    mut v___y_2725_: *mut crate::leanh::LeanObject,
    mut v___y_2726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2728_: u8 = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: u8 = 0;
    let mut v___x_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: usize = 0;
    let mut v___x_2741_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2728_ = lean_usize_dec_lt(v_i_2723_, v_sz_2722_);
                if v___x_2728_ == 0 {
                    crate::leanh::lean_dec(v_declName_2720_);
                    v___x_2729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2729_, 0, v_b_2724_);
                    return v___x_2729_;
                } else {
                    v___x_2730_ = l_Lean_Environment_header(v___x_2719_);
                    v_modules_2731_ = crate::leanh::lean_ctor_get(v___x_2730_, 3);
                    crate::leanh::lean_inc_ref(v_modules_2731_);
                    crate::leanh::lean_dec_ref(v___x_2730_);
                    v___x_2732_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_2733_ = lean_array_uget_borrowed(v_as_2721_, v_i_2723_);
                    v___x_2734_ = lean_array_get(v___x_2732_, v_modules_2731_, v_a_2733_);
                    crate::leanh::lean_dec_ref(v_modules_2731_);
                    v_toImport_2735_ = crate::leanh::lean_ctor_get(v___x_2734_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_2735_);
                    crate::leanh::lean_dec(v___x_2734_);
                    v_module_2736_ = crate::leanh::lean_ctor_get(v_toImport_2735_, 0);
                    crate::leanh::lean_inc(v_module_2736_);
                    crate::leanh::lean_dec_ref(v_toImport_2735_);
                    v___x_2737_ = 0;
                    crate::leanh::lean_inc(v_declName_2720_);
                    v___x_2738_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6(v_module_2736_, v___x_2737_, v_declName_2720_, v___y_2725_, v___y_2726_);
                    if crate::leanh::lean_obj_tag(v___x_2738_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2738_, 1);
                        v___x_2739_ = crate::leanh::lean_box(0);
                        v___x_2740_ = 1usize;
                        v___x_2741_ = lean_usize_add(v_i_2723_, v___x_2740_);
                        v_i_2723_ = v___x_2741_;
                        v_b_2724_ = v___x_2739_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2720_);
                        return v___x_2738_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__7___boxed(
    mut v___x_2743_: *mut crate::leanh::LeanObject,
    mut v_declName_2744_: *mut crate::leanh::LeanObject,
    mut v_as_2745_: *mut crate::leanh::LeanObject,
    mut v_sz_2746_: *mut crate::leanh::LeanObject,
    mut v_i_2747_: *mut crate::leanh::LeanObject,
    mut v_b_2748_: *mut crate::leanh::LeanObject,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
    mut v___y_2750_: *mut crate::leanh::LeanObject,
    mut v___y_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2752_: usize = 0;
    let mut v_i_boxed_2753_: usize = 0;
    let mut v_res_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2752_ = crate::leanh::lean_unbox_usize(v_sz_2746_);
    crate::leanh::lean_dec(v_sz_2746_);
    v_i_boxed_2753_ = crate::leanh::lean_unbox_usize(v_i_2747_);
    crate::leanh::lean_dec(v_i_2747_);
    v_res_2754_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__7(v___x_2743_, v_declName_2744_, v_as_2745_, v_sz_boxed_2752_, v_i_boxed_2753_, v_b_2748_, v___y_2749_, v___y_2750_);
    crate::leanh::lean_dec(v___y_2750_);
    crate::leanh::lean_dec_ref(v___y_2749_);
    crate::leanh::lean_dec_ref(v_as_2745_);
    crate::leanh::lean_dec_ref(v___x_2743_);
    return v_res_2754_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2757_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__1;
    v___x_2758_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__0;
    v___x_2759_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2758_,
        v___x_2757_,
    );
    return v___x_2759_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3(
    mut v_declName_2762_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2763_: u8,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2775_: usize = 0;
    let mut v___x_2776_: usize = 0;
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2780_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2784_: u8 = 0;
    let mut v_unused_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2797_: u8 = 0;
    let mut v_toImport_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2808_: u8 = 0;
    let mut v___x_2809_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2767_ = lean_st_ref_get(v___y_2765_);
                v_env_2771_ = crate::leanh::lean_ctor_get(v___x_2767_, 0);
                crate::leanh::lean_inc_ref(v_env_2771_);
                crate::leanh::lean_dec(v___x_2767_);
                v___x_2786_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2771_, v_declName_2762_);
                if crate::leanh::lean_obj_tag(v___x_2786_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_2771_);
                    crate::leanh::lean_dec(v_declName_2762_);
                    state = 1;
                    continue;
                } else {
                    v_val_2787_ = crate::leanh::lean_ctor_get(v___x_2786_, 0);
                    crate::leanh::lean_inc(v_val_2787_);
                    crate::leanh::lean_dec_ref_known(v___x_2786_, 1);
                    v___x_2788_ = l_Lean_Environment_header(v_env_2771_);
                    v_modules_2789_ = crate::leanh::lean_ctor_get(v___x_2788_, 3);
                    crate::leanh::lean_inc_ref(v_modules_2789_);
                    crate::leanh::lean_dec_ref(v___x_2788_);
                    v___x_2790_ = lean_array_get_size(v_modules_2789_);
                    v___x_2791_ = lean_nat_dec_lt(v_val_2787_, v___x_2790_);
                    if v___x_2791_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_2789_);
                        crate::leanh::lean_dec(v_val_2787_);
                        crate::leanh::lean_dec_ref(v_env_2771_);
                        crate::leanh::lean_dec(v_declName_2762_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2792_ = lean_st_ref_get(v___y_2765_);
                        v_env_2793_ = crate::leanh::lean_ctor_get(v___x_2792_, 0);
                        crate::leanh::lean_inc_ref(v_env_2793_);
                        crate::leanh::lean_dec(v___x_2792_);
                        v___x_2794_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__2);
                        v___x_2795_ = lean_array_fget(v_modules_2789_, v_val_2787_);
                        crate::leanh::lean_dec(v_val_2787_);
                        crate::leanh::lean_dec_ref(v_modules_2789_);
                        if v_isMeta_2763_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_2793_);
                            v___y_2797_ = v_isMeta_2763_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_2762_);
                            v___x_2808_ = l_Lean_isMarkedMeta(v_env_2793_, v_declName_2762_);
                            if v___x_2808_ == 0 {
                                v___y_2797_ = v_isMeta_2763_;
                                state = 5;
                                continue;
                            } else {
                                v___x_2809_ = 0;
                                v___y_2797_ = v___x_2809_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2769_ = crate::leanh::lean_box(0);
                v___x_2770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2770_, 0, v___x_2769_);
                return v___x_2770_;
            }
            2 => {
                v___x_2774_ = crate::leanh::lean_box(0);
                v_sz_2775_ = lean_array_size(v___y_2773_);
                v___x_2776_ = 0usize;
                v___x_2777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__7(v_env_2771_, v_declName_2762_, v___y_2773_, v_sz_2775_, v___x_2776_, v___x_2774_, v___y_2764_, v___y_2765_);
                crate::leanh::lean_dec_ref(v___y_2773_);
                crate::leanh::lean_dec_ref(v_env_2771_);
                if crate::leanh::lean_obj_tag(v___x_2777_) == 0 {
                    v_isSharedCheck_2784_ = (!crate::leanh::lean_is_exclusive(v___x_2777_)) as u8;
                    if v_isSharedCheck_2784_ == 0 {
                        v_unused_2785_ = crate::leanh::lean_ctor_get(v___x_2777_, 0);
                        crate::leanh::lean_dec(v_unused_2785_);
                        v___x_2779_ = v___x_2777_;
                        v_isShared_2780_ = v_isSharedCheck_2784_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2777_);
                        v___x_2779_ = crate::leanh::lean_box(0);
                        v_isShared_2780_ = v_isSharedCheck_2784_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2777_;
                }
            }
            3 => {
                if v_isShared_2780_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2779_, 0, v___x_2774_);
                    v___x_2782_ = v___x_2779_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2774_);
                    v___x_2782_ = v_reuseFailAlloc_2783_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2782_;
            }
            5 => {
                v_toImport_2798_ = crate::leanh::lean_ctor_get(v___x_2795_, 0);
                crate::leanh::lean_inc_ref(v_toImport_2798_);
                crate::leanh::lean_dec(v___x_2795_);
                v_module_2799_ = crate::leanh::lean_ctor_get(v_toImport_2798_, 0);
                crate::leanh::lean_inc(v_module_2799_);
                crate::leanh::lean_dec_ref(v_toImport_2798_);
                crate::leanh::lean_inc(v_declName_2762_);
                v___x_2800_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6(v_module_2799_, v___y_2797_, v_declName_2762_, v___y_2764_, v___y_2765_);
                if crate::leanh::lean_obj_tag(v___x_2800_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2800_, 1);
                    v___x_2801_ = l_Lean_indirectModUseExt;
                    v___x_2802_ = crate::leanh::lean_box(1);
                    v___x_2803_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_2771_);
                    v___x_2804_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_2794_,
                        v___x_2801_,
                        v_env_2771_,
                        v___x_2802_,
                        v___x_2803_,
                    );
                    v___x_2805_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg(v___x_2804_, v_declName_2762_);
                    crate::leanh::lean_dec(v___x_2804_);
                    if crate::leanh::lean_obj_tag(v___x_2805_) == 0 {
                        v___x_2806_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___closed__3;
                        v___y_2773_ = v___x_2806_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2807_ = crate::leanh::lean_ctor_get(v___x_2805_, 0);
                        crate::leanh::lean_inc(v_val_2807_);
                        crate::leanh::lean_dec_ref_known(v___x_2805_, 1);
                        v___y_2773_ = v_val_2807_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2771_);
                    crate::leanh::lean_dec(v_declName_2762_);
                    return v___x_2800_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3___boxed(
    mut v_declName_2810_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
    mut v___y_2813_: *mut crate::leanh::LeanObject,
    mut v___y_2814_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_2815_: u8 = 0;
    let mut v_res_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2815_ = (crate::leanh::lean_unbox(v_isMeta_2811_) as u8);
    v_res_2816_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3(v_declName_2810_, v_isMeta_boxed_2815_, v___y_2812_, v___y_2813_);
    crate::leanh::lean_dec(v___y_2813_);
    crate::leanh::lean_dec_ref(v___y_2812_);
    return v_res_2816_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4___redArg(
    mut v_as_x27_2817_: *mut crate::leanh::LeanObject,
    mut v_b_2818_: *mut crate::leanh::LeanObject,
    mut v___y_2819_: *mut crate::leanh::LeanObject,
    mut v___y_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_2817_) == 0 {
                    v___x_2822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2822_, 0, v_b_2818_);
                    return v___x_2822_;
                } else {
                    v_head_2823_ = crate::leanh::lean_ctor_get(v_as_x27_2817_, 0);
                    v_tail_2824_ = crate::leanh::lean_ctor_get(v_as_x27_2817_, 1);
                    v___x_2825_ = 1;
                    crate::leanh::lean_inc(v_head_2823_);
                    v___x_2826_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3(v_head_2823_, v___x_2825_, v___y_2819_, v___y_2820_);
                    if crate::leanh::lean_obj_tag(v___x_2826_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2826_, 1);
                        v___x_2827_ = crate::leanh::lean_box(0);
                        v_as_x27_2817_ = v_tail_2824_;
                        v_b_2818_ = v___x_2827_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2826_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_2829_: *mut crate::leanh::LeanObject,
    mut v_b_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2834_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4___redArg(v_as_x27_2829_, v_b_2830_, v___y_2831_, v___y_2832_);
    crate::leanh::lean_dec(v___y_2832_);
    crate::leanh::lean_dec_ref(v___y_2831_);
    crate::leanh::lean_dec(v_as_x27_2829_);
    return v_res_2834_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__5(
    mut v_as_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
    mut v___y_2837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2852_: u8 = 0;
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: u8 = 0;
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_2835_) == 0 {
                    v___x_2839_ = crate::leanh::lean_box(0);
                    v___x_2840_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2840_, 0, v___x_2839_);
                    return v___x_2840_;
                } else {
                    v_head_2841_ = crate::leanh::lean_ctor_get(v_as_2835_, 0);
                    crate::leanh::lean_inc(v_head_2841_);
                    v_tail_2842_ = crate::leanh::lean_ctor_get(v_as_2835_, 1);
                    crate::leanh::lean_inc(v_tail_2842_);
                    crate::leanh::lean_dec_ref_known(v_as_2835_, 2);
                    v_fst_2843_ = crate::leanh::lean_ctor_get(v_head_2841_, 0);
                    crate::leanh::lean_inc(v_fst_2843_);
                    v_snd_2844_ = crate::leanh::lean_ctor_get(v_head_2841_, 1);
                    crate::leanh::lean_inc(v_snd_2844_);
                    crate::leanh::lean_dec(v_head_2841_);
                    v___x_2845_ = l_Lean_inheritedTraceOptions;
                    v___x_2846_ = lean_st_ref_get(v___x_2845_);
                    v___x_2847_ = lean_st_ref_get(v___y_2837_);
                    v_scopes_2848_ = crate::leanh::lean_ctor_get(v___x_2847_, 2);
                    crate::leanh::lean_inc(v_scopes_2848_);
                    crate::leanh::lean_dec(v___x_2847_);
                    v___x_2849_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_2850_ = l_List_head_x21___redArg(v___x_2849_, v_scopes_2848_);
                    crate::leanh::lean_dec(v_scopes_2848_);
                    v_opts_2851_ = crate::leanh::lean_ctor_get(v___x_2850_, 1);
                    crate::leanh::lean_inc_ref(v_opts_2851_);
                    crate::leanh::lean_dec(v___x_2850_);
                    v_hasTrace_2852_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_2851_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2852_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_2851_);
                        crate::leanh::lean_dec(v___x_2846_);
                        crate::leanh::lean_dec(v_snd_2844_);
                        crate::leanh::lean_dec(v_fst_2843_);
                        v_as_2835_ = v_tail_2842_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2854_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6___closed__11;
                        crate::leanh::lean_inc(v_fst_2843_);
                        v___x_2855_ = l_Lean_Name_append(v___x_2854_, v_fst_2843_);
                        v___x_2856_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_2846_,
                            v_opts_2851_,
                            v___x_2855_,
                        );
                        crate::leanh::lean_dec(v___x_2855_);
                        crate::leanh::lean_dec_ref(v_opts_2851_);
                        crate::leanh::lean_dec(v___x_2846_);
                        if v___x_2856_ == 0 {
                            crate::leanh::lean_dec(v_snd_2844_);
                            crate::leanh::lean_dec(v_fst_2843_);
                            v_as_2835_ = v_tail_2842_;
                            state = 0;
                            continue;
                        } else {
                            v___x_2858_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2858_, 0, v_snd_2844_);
                            v___x_2859_ = l_Lean_MessageData_ofFormat(v___x_2858_);
                            v___x_2860_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1(v_fst_2843_, v___x_2859_, v___y_2836_, v___y_2837_);
                            if crate::leanh::lean_obj_tag(v___x_2860_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2860_, 1);
                                v_as_2835_ = v_tail_2842_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_2842_);
                                return v___x_2860_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__5___boxed(
    mut v_as_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2866_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__5(v_as_2862_, v___y_2863_, v___y_2864_);
    crate::leanh::lean_dec(v___y_2864_);
    crate::leanh::lean_dec_ref(v___y_2863_);
    return v_res_2866_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__20(
    mut v_opts_2867_: *mut crate::leanh::LeanObject,
    mut v_opt_2868_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2869_ = crate::leanh::lean_ctor_get(v_opt_2868_, 0);
    v_defValue_2870_ = crate::leanh::lean_ctor_get(v_opt_2868_, 1);
    v_map_2871_ = crate::leanh::lean_ctor_get(v_opts_2867_, 0);
    v___x_2872_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2871_,
            v_name_2869_,
        );
    if crate::leanh::lean_obj_tag(v___x_2872_) == 0 {
        let mut v___x_2873_: u8 = 0;
        v___x_2873_ = (crate::leanh::lean_unbox(v_defValue_2870_) as u8);
        return v___x_2873_;
    } else {
        let mut v_val_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2874_ = crate::leanh::lean_ctor_get(v___x_2872_, 0);
        crate::leanh::lean_inc(v_val_2874_);
        crate::leanh::lean_dec_ref_known(v___x_2872_, 1);
        if crate::leanh::lean_obj_tag(v_val_2874_) == 1 {
            let mut v_v_2875_: u8 = 0;
            v_v_2875_ = crate::leanh::lean_ctor_get_uint8(v_val_2874_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2874_, 0);
            return v_v_2875_;
        } else {
            let mut v___x_2876_: u8 = 0;
            crate::leanh::lean_dec(v_val_2874_);
            v___x_2876_ = (crate::leanh::lean_unbox(v_defValue_2870_) as u8);
            return v___x_2876_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__20___boxed(
    mut v_opts_2877_: *mut crate::leanh::LeanObject,
    mut v_opt_2878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2879_: u8 = 0;
    let mut v_r_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2879_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__20(v_opts_2877_, v_opt_2878_);
    crate::leanh::lean_dec_ref(v_opt_2878_);
    crate::leanh::lean_dec_ref(v_opts_2877_);
    v_r_2880_ = crate::leanh::lean_box((v_res_2879_) as usize);
    return v_r_2880_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2881_ = crate::leanh::lean_box(1);
    v___x_2882_ = l_Lean_MessageData_ofFormat(v___x_2881_);
    return v___x_2882_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2886_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__2;
    v___x_2887_ = l_Lean_MessageData_ofFormat(v___x_2886_);
    return v___x_2887_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21(
    mut v_x_2888_: *mut crate::leanh::LeanObject,
    mut v_x_2889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2894_: u8 = 0;
    let mut v_before_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2898_: u8 = 0;
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2911_: u8 = 0;
    let mut v_unused_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2913_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2889_) == 0 {
                    return v_x_2888_;
                } else {
                    v_head_2890_ = crate::leanh::lean_ctor_get(v_x_2889_, 0);
                    v_tail_2891_ = crate::leanh::lean_ctor_get(v_x_2889_, 1);
                    v_isSharedCheck_2913_ = (!crate::leanh::lean_is_exclusive(v_x_2889_)) as u8;
                    if v_isSharedCheck_2913_ == 0 {
                        v___x_2893_ = v_x_2889_;
                        v_isShared_2894_ = v_isSharedCheck_2913_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2891_);
                        crate::leanh::lean_inc(v_head_2890_);
                        crate::leanh::lean_dec(v_x_2889_);
                        v___x_2893_ = crate::leanh::lean_box(0);
                        v_isShared_2894_ = v_isSharedCheck_2913_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2895_ = crate::leanh::lean_ctor_get(v_head_2890_, 0);
                v_isSharedCheck_2911_ = (!crate::leanh::lean_is_exclusive(v_head_2890_)) as u8;
                if v_isSharedCheck_2911_ == 0 {
                    v_unused_2912_ = crate::leanh::lean_ctor_get(v_head_2890_, 1);
                    crate::leanh::lean_dec(v_unused_2912_);
                    v___x_2897_ = v_head_2890_;
                    v_isShared_2898_ = v_isSharedCheck_2911_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2895_);
                    crate::leanh::lean_dec(v_head_2890_);
                    v___x_2897_ = crate::leanh::lean_box(0);
                    v_isShared_2898_ = v_isSharedCheck_2911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0);
                if v_isShared_2898_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2897_, 7);
                    crate::leanh::lean_ctor_set(v___x_2897_, 1, v___x_2899_);
                    crate::leanh::lean_ctor_set(v___x_2897_, 0, v_x_2888_);
                    v___x_2901_ = v___x_2897_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2910_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_x_2888_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2910_, 1, v___x_2899_);
                    v___x_2901_ = v_reuseFailAlloc_2910_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2902_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__3);
                if v_isShared_2894_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2893_, 7);
                    crate::leanh::lean_ctor_set(v___x_2893_, 1, v___x_2902_);
                    crate::leanh::lean_ctor_set(v___x_2893_, 0, v___x_2901_);
                    v___x_2904_ = v___x_2893_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2909_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 0, v___x_2901_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 1, v___x_2902_);
                    v___x_2904_ = v_reuseFailAlloc_2909_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2905_ = l_Lean_MessageData_ofSyntax(v_before_2895_);
                v___x_2906_ = l_Lean_indentD(v___x_2905_);
                v___x_2907_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2907_, 0, v___x_2904_);
                crate::leanh::lean_ctor_set(v___x_2907_, 1, v___x_2906_);
                v_x_2888_ = v___x_2907_;
                v_x_2889_ = v_tail_2891_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2917_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__1;
    v___x_2918_ = l_Lean_MessageData_ofFormat(v___x_2917_);
    return v___x_2918_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg(
    mut v_msgData_2919_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: u8 = 0;
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_unused_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2923_ = lean_st_ref_get(v___y_2921_);
                v_scopes_2924_ = crate::leanh::lean_ctor_get(v___x_2923_, 2);
                crate::leanh::lean_inc(v_scopes_2924_);
                crate::leanh::lean_dec(v___x_2923_);
                v___x_2925_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_2926_ = l_List_head_x21___redArg(v___x_2925_, v_scopes_2924_);
                crate::leanh::lean_dec(v_scopes_2924_);
                v_opts_2927_ = crate::leanh::lean_ctor_get(v___x_2926_, 1);
                crate::leanh::lean_inc_ref(v_opts_2927_);
                crate::leanh::lean_dec(v___x_2926_);
                v___x_2928_ = l_Lean_Elab_pp_macroStack;
                v___x_2929_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__20(v_opts_2927_, v___x_2928_);
                crate::leanh::lean_dec_ref(v_opts_2927_);
                if v___x_2929_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2920_);
                    v___x_2930_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2930_, 0, v_msgData_2919_);
                    return v___x_2930_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2920_) == 0 {
                        v___x_2931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2931_, 0, v_msgData_2919_);
                        return v___x_2931_;
                    } else {
                        v_head_2932_ = crate::leanh::lean_ctor_get(v_macroStack_2920_, 0);
                        crate::leanh::lean_inc(v_head_2932_);
                        v_after_2933_ = crate::leanh::lean_ctor_get(v_head_2932_, 1);
                        v_isSharedCheck_2948_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2932_)) as u8;
                        if v_isSharedCheck_2948_ == 0 {
                            v_unused_2949_ = crate::leanh::lean_ctor_get(v_head_2932_, 0);
                            crate::leanh::lean_dec(v_unused_2949_);
                            v___x_2935_ = v_head_2932_;
                            v_isShared_2936_ = v_isSharedCheck_2948_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2933_);
                            crate::leanh::lean_dec(v_head_2932_);
                            v___x_2935_ = crate::leanh::lean_box(0);
                            v_isShared_2936_ = v_isSharedCheck_2948_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2937_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21___closed__0);
                if v_isShared_2936_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2935_, 7);
                    crate::leanh::lean_ctor_set(v___x_2935_, 1, v___x_2937_);
                    crate::leanh::lean_ctor_set(v___x_2935_, 0, v_msgData_2919_);
                    v___x_2939_ = v___x_2935_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_msgData_2919_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2947_, 1, v___x_2937_);
                    v___x_2939_ = v_reuseFailAlloc_2947_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2940_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___closed__2);
                v___x_2941_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2941_, 0, v___x_2939_);
                crate::leanh::lean_ctor_set(v___x_2941_, 1, v___x_2940_);
                v___x_2942_ = l_Lean_MessageData_ofSyntax(v_after_2933_);
                v___x_2943_ = l_Lean_indentD(v___x_2942_);
                v_msgData_2944_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2944_, 0, v___x_2941_);
                crate::leanh::lean_ctor_set(v_msgData_2944_, 1, v___x_2943_);
                v___x_2945_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18_spec__21(v_msgData_2944_, v_macroStack_2920_);
                v___x_2946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2946_, 0, v___x_2945_);
                return v___x_2946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg___boxed(
    mut v_msgData_2950_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2954_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg(v_msgData_2950_, v_macroStack_2951_, v___y_2952_);
    crate::leanh::lean_dec(v___y_2952_);
    return v_res_2954_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12___redArg(
    mut v_msg_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
    mut v___y_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2969_: u8 = 0;
    let mut v___x_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2974_: u8 = 0;
    let mut v_a_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2978_: u8 = 0;
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2982_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2959_ = l_Lean_Elab_Command_getRef___redArg(v___y_2956_);
                if crate::leanh::lean_obj_tag(v___x_2959_) == 0 {
                    v_a_2960_ = crate::leanh::lean_ctor_get(v___x_2959_, 0);
                    crate::leanh::lean_inc(v_a_2960_);
                    crate::leanh::lean_dec_ref_known(v___x_2959_, 1);
                    v_macroStack_2961_ = crate::leanh::lean_ctor_get(v___y_2956_, 4);
                    v___x_2962_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg(v_msg_2955_, v___y_2957_);
                    v_a_2963_ = crate::leanh::lean_ctor_get(v___x_2962_, 0);
                    crate::leanh::lean_inc(v_a_2963_);
                    crate::leanh::lean_dec_ref(v___x_2962_);
                    v___x_2964_ = l_Lean_Elab_getBetterRef(v_a_2960_, v_macroStack_2961_);
                    crate::leanh::lean_dec(v_a_2960_);
                    crate::leanh::lean_inc(v_macroStack_2961_);
                    v___x_2965_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg(v_a_2963_, v_macroStack_2961_, v___y_2957_);
                    v_a_2966_ = crate::leanh::lean_ctor_get(v___x_2965_, 0);
                    v_isSharedCheck_2974_ = (!crate::leanh::lean_is_exclusive(v___x_2965_)) as u8;
                    if v_isSharedCheck_2974_ == 0 {
                        v___x_2968_ = v___x_2965_;
                        v_isShared_2969_ = v_isSharedCheck_2974_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2966_);
                        crate::leanh::lean_dec(v___x_2965_);
                        v___x_2968_ = crate::leanh::lean_box(0);
                        v_isShared_2969_ = v_isSharedCheck_2974_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2955_);
                    v_a_2975_ = crate::leanh::lean_ctor_get(v___x_2959_, 0);
                    v_isSharedCheck_2982_ = (!crate::leanh::lean_is_exclusive(v___x_2959_)) as u8;
                    if v_isSharedCheck_2982_ == 0 {
                        v___x_2977_ = v___x_2959_;
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2975_);
                        crate::leanh::lean_dec(v___x_2959_);
                        v___x_2977_ = crate::leanh::lean_box(0);
                        v_isShared_2978_ = v_isSharedCheck_2982_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2970_, 0, v___x_2964_);
                crate::leanh::lean_ctor_set(v___x_2970_, 1, v_a_2966_);
                if v_isShared_2969_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2968_, 1);
                    crate::leanh::lean_ctor_set(v___x_2968_, 0, v___x_2970_);
                    v___x_2972_ = v___x_2968_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2973_, 0, v___x_2970_);
                    v___x_2972_ = v_reuseFailAlloc_2973_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2972_;
            }
            3 => {
                if v_isShared_2978_ == 0 {
                    v___x_2980_ = v___x_2977_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2981_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
                    v___x_2980_ = v_reuseFailAlloc_2981_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12___redArg___boxed(
    mut v_msg_2983_: *mut crate::leanh::LeanObject,
    mut v___y_2984_: *mut crate::leanh::LeanObject,
    mut v___y_2985_: *mut crate::leanh::LeanObject,
    mut v___y_2986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2987_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12___redArg(v_msg_2983_, v___y_2984_, v___y_2985_);
    crate::leanh::lean_dec(v___y_2985_);
    crate::leanh::lean_dec_ref(v___y_2984_);
    return v_res_2987_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6___redArg(
    mut v_ref_2988_: *mut crate::leanh::LeanObject,
    mut v_msg_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_3002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3004_: u8 = 0;
    let mut v_ref_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3011_: u8 = 0;
    let mut v___x_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3015_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2993_ = l_Lean_Elab_Command_getRef___redArg(v___y_2990_);
                if crate::leanh::lean_obj_tag(v___x_2993_) == 0 {
                    v_a_2994_ = crate::leanh::lean_ctor_get(v___x_2993_, 0);
                    crate::leanh::lean_inc(v_a_2994_);
                    crate::leanh::lean_dec_ref_known(v___x_2993_, 1);
                    v_fileName_2995_ = crate::leanh::lean_ctor_get(v___y_2990_, 0);
                    v_fileMap_2996_ = crate::leanh::lean_ctor_get(v___y_2990_, 1);
                    v_currRecDepth_2997_ = crate::leanh::lean_ctor_get(v___y_2990_, 2);
                    v_cmdPos_2998_ = crate::leanh::lean_ctor_get(v___y_2990_, 3);
                    v_macroStack_2999_ = crate::leanh::lean_ctor_get(v___y_2990_, 4);
                    v_quotContext_x3f_3000_ = crate::leanh::lean_ctor_get(v___y_2990_, 5);
                    v_currMacroScope_3001_ = crate::leanh::lean_ctor_get(v___y_2990_, 6);
                    v_snap_x3f_3002_ = crate::leanh::lean_ctor_get(v___y_2990_, 8);
                    v_cancelTk_x3f_3003_ = crate::leanh::lean_ctor_get(v___y_2990_, 9);
                    v_suppressElabErrors_3004_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_2990_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_3005_ = l_Lean_replaceRef(v_ref_2988_, v_a_2994_);
                    crate::leanh::lean_dec(v_a_2994_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_3003_);
                    crate::leanh::lean_inc(v_snap_x3f_3002_);
                    crate::leanh::lean_inc(v_currMacroScope_3001_);
                    crate::leanh::lean_inc(v_quotContext_x3f_3000_);
                    crate::leanh::lean_inc(v_macroStack_2999_);
                    crate::leanh::lean_inc(v_cmdPos_2998_);
                    crate::leanh::lean_inc(v_currRecDepth_2997_);
                    crate::leanh::lean_inc_ref(v_fileMap_2996_);
                    crate::leanh::lean_inc_ref(v_fileName_2995_);
                    v___x_3006_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_3006_, 0, v_fileName_2995_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 1, v_fileMap_2996_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 2, v_currRecDepth_2997_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 3, v_cmdPos_2998_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 4, v_macroStack_2999_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 5, v_quotContext_x3f_3000_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 6, v_currMacroScope_3001_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 7, v_ref_3005_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 8, v_snap_x3f_3002_);
                    crate::leanh::lean_ctor_set(v___x_3006_, 9, v_cancelTk_x3f_3003_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_3006_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_3004_,
                    );
                    v___x_3007_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12___redArg(v_msg_2989_, v___x_3006_, v___y_2991_);
                    crate::leanh::lean_dec_ref_known(v___x_3006_, 10);
                    return v___x_3007_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_2989_);
                    v_a_3008_ = crate::leanh::lean_ctor_get(v___x_2993_, 0);
                    v_isSharedCheck_3015_ = (!crate::leanh::lean_is_exclusive(v___x_2993_)) as u8;
                    if v_isSharedCheck_3015_ == 0 {
                        v___x_3010_ = v___x_2993_;
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3008_);
                        crate::leanh::lean_dec(v___x_2993_);
                        v___x_3010_ = crate::leanh::lean_box(0);
                        v_isShared_3011_ = v_isSharedCheck_3015_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3011_ == 0 {
                    v___x_3013_ = v___x_3010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3014_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
                    v___x_3013_ = v_reuseFailAlloc_3014_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3013_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6___redArg___boxed(
    mut v_ref_3016_: *mut crate::leanh::LeanObject,
    mut v_msg_3017_: *mut crate::leanh::LeanObject,
    mut v___y_3018_: *mut crate::leanh::LeanObject,
    mut v___y_3019_: *mut crate::leanh::LeanObject,
    mut v___y_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3021_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6___redArg(v_ref_3016_, v_msg_3017_, v___y_3018_, v___y_3019_);
    crate::leanh::lean_dec(v___y_3019_);
    crate::leanh::lean_dec_ref(v___y_3018_);
    crate::leanh::lean_dec(v_ref_3016_);
    return v_res_3021_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg(
    mut v_x_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3082_: u8 = 0;
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3090_: u8 = 0;
    let mut v___x_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3094_: u8 = 0;
    let mut v_unused_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3099_: u8 = 0;
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3103_: u8 = 0;
    let mut v_reuseFailAlloc_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_unused_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3114_: u8 = 0;
    let mut v_a_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: u8 = 0;
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3131_: u8 = 0;
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v_a_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3139_: u8 = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut v_a_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3147_: u8 = 0;
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_a_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3155_: u8 = 0;
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3027_ = lean_st_ref_get(v___y_3025_);
                v_env_3028_ = crate::leanh::lean_ctor_get(v___x_3027_, 0);
                crate::leanh::lean_inc_ref(v_env_3028_);
                crate::leanh::lean_dec(v___x_3027_);
                v___x_3029_ = lean_st_ref_get(v___y_3025_);
                v_scopes_3030_ = crate::leanh::lean_ctor_get(v___x_3029_, 2);
                crate::leanh::lean_inc(v_scopes_3030_);
                crate::leanh::lean_dec(v___x_3029_);
                v___x_3031_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3032_ = l_List_head_x21___redArg(v___x_3031_, v_scopes_3030_);
                crate::leanh::lean_dec(v_scopes_3030_);
                v_opts_3033_ = crate::leanh::lean_ctor_get(v___x_3032_, 1);
                crate::leanh::lean_inc_ref(v_opts_3033_);
                crate::leanh::lean_dec(v___x_3032_);
                v___x_3034_ = l_Lean_Elab_Command_getScope___redArg(v___y_3025_);
                if crate::leanh::lean_obj_tag(v___x_3034_) == 0 {
                    v_a_3035_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                    crate::leanh::lean_inc(v_a_3035_);
                    crate::leanh::lean_dec_ref_known(v___x_3034_, 1);
                    v_currNamespace_3036_ = crate::leanh::lean_ctor_get(v_a_3035_, 2);
                    crate::leanh::lean_inc(v_currNamespace_3036_);
                    crate::leanh::lean_dec(v_a_3035_);
                    v___x_3037_ = l_Lean_Elab_Command_getScope___redArg(v___y_3025_);
                    if crate::leanh::lean_obj_tag(v___x_3037_) == 0 {
                        v_a_3038_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                        crate::leanh::lean_inc(v_a_3038_);
                        crate::leanh::lean_dec_ref_known(v___x_3037_, 1);
                        v_openDecls_3039_ = crate::leanh::lean_ctor_get(v_a_3038_, 3);
                        crate::leanh::lean_inc(v_openDecls_3039_);
                        crate::leanh::lean_dec(v_a_3038_);
                        v___x_3040_ = l_Lean_Elab_Command_getRef___redArg(v___y_3024_);
                        if crate::leanh::lean_obj_tag(v___x_3040_) == 0 {
                            v_a_3041_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
                            crate::leanh::lean_inc(v_a_3041_);
                            crate::leanh::lean_dec_ref_known(v___x_3040_, 1);
                            v___x_3042_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3024_);
                            if crate::leanh::lean_obj_tag(v___x_3042_) == 0 {
                                v_a_3043_ = crate::leanh::lean_ctor_get(v___x_3042_, 0);
                                crate::leanh::lean_inc(v_a_3043_);
                                crate::leanh::lean_dec_ref_known(v___x_3042_, 1);
                                v_currRecDepth_3044_ = crate::leanh::lean_ctor_get(v___y_3024_, 2);
                                v_quotContext_x3f_3045_ =
                                    crate::leanh::lean_ctor_get(v___y_3024_, 5);
                                crate::leanh::lean_inc_ref_n(v_env_3028_, 3);
                                v___f_3046_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                                crate::leanh::lean_closure_set(v___f_3046_, 0, v_env_3028_);
                                v___f_3047_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                                crate::leanh::lean_closure_set(v___f_3047_, 0, v_env_3028_);
                                crate::leanh::lean_inc_n(v_currNamespace_3036_, 2);
                                v___f_3048_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                                crate::leanh::lean_closure_set(
                                    v___f_3048_,
                                    0,
                                    v_currNamespace_3036_,
                                );
                                crate::leanh::lean_inc(v_openDecls_3039_);
                                v___f_3049_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                                crate::leanh::lean_closure_set(v___f_3049_, 0, v_env_3028_);
                                crate::leanh::lean_closure_set(
                                    v___f_3049_,
                                    1,
                                    v_currNamespace_3036_,
                                );
                                crate::leanh::lean_closure_set(v___f_3049_, 2, v_openDecls_3039_);
                                v___f_3050_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                                crate::leanh::lean_closure_set(v___f_3050_, 0, v_env_3028_);
                                crate::leanh::lean_closure_set(v___f_3050_, 1, v_opts_3033_);
                                crate::leanh::lean_closure_set(
                                    v___f_3050_,
                                    2,
                                    v_currNamespace_3036_,
                                );
                                crate::leanh::lean_closure_set(v___f_3050_, 3, v_openDecls_3039_);
                                v_methods_3051_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_methods_3051_, 0, v___f_3047_);
                                crate::leanh::lean_ctor_set(v_methods_3051_, 1, v___f_3048_);
                                crate::leanh::lean_ctor_set(v_methods_3051_, 2, v___f_3046_);
                                crate::leanh::lean_ctor_set(v_methods_3051_, 3, v___f_3049_);
                                crate::leanh::lean_ctor_set(v_methods_3051_, 4, v___f_3050_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_3045_) == 0 {
                                    v___x_3125_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_3025_);
                                    v_a_3126_ = crate::leanh::lean_ctor_get(v___x_3125_, 0);
                                    crate::leanh::lean_inc(v_a_3126_);
                                    crate::leanh::lean_dec_ref(v___x_3125_);
                                    v_a_3053_ = v_a_3126_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_3127_ =
                                        crate::leanh::lean_ctor_get(v_quotContext_x3f_3045_, 0);
                                    crate::leanh::lean_inc(v_val_3127_);
                                    v_a_3053_ = v_val_3127_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3041_);
                                crate::leanh::lean_dec(v_openDecls_3039_);
                                crate::leanh::lean_dec(v_currNamespace_3036_);
                                crate::leanh::lean_dec_ref(v_opts_3033_);
                                crate::leanh::lean_dec_ref(v_env_3028_);
                                crate::leanh::lean_dec_ref(v_x_3023_);
                                v_a_3128_ = crate::leanh::lean_ctor_get(v___x_3042_, 0);
                                v_isSharedCheck_3135_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3042_)) as u8;
                                if v_isSharedCheck_3135_ == 0 {
                                    v___x_3130_ = v___x_3042_;
                                    v_isShared_3131_ = v_isSharedCheck_3135_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3128_);
                                    crate::leanh::lean_dec(v___x_3042_);
                                    v___x_3130_ = crate::leanh::lean_box(0);
                                    v_isShared_3131_ = v_isSharedCheck_3135_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_openDecls_3039_);
                            crate::leanh::lean_dec(v_currNamespace_3036_);
                            crate::leanh::lean_dec_ref(v_opts_3033_);
                            crate::leanh::lean_dec_ref(v_env_3028_);
                            crate::leanh::lean_dec_ref(v_x_3023_);
                            v_a_3136_ = crate::leanh::lean_ctor_get(v___x_3040_, 0);
                            v_isSharedCheck_3143_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3040_)) as u8;
                            if v_isSharedCheck_3143_ == 0 {
                                v___x_3138_ = v___x_3040_;
                                v_isShared_3139_ = v_isSharedCheck_3143_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3136_);
                                crate::leanh::lean_dec(v___x_3040_);
                                v___x_3138_ = crate::leanh::lean_box(0);
                                v_isShared_3139_ = v_isSharedCheck_3143_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_currNamespace_3036_);
                        crate::leanh::lean_dec_ref(v_opts_3033_);
                        crate::leanh::lean_dec_ref(v_env_3028_);
                        crate::leanh::lean_dec_ref(v_x_3023_);
                        v_a_3144_ = crate::leanh::lean_ctor_get(v___x_3037_, 0);
                        v_isSharedCheck_3151_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3037_)) as u8;
                        if v_isSharedCheck_3151_ == 0 {
                            v___x_3146_ = v___x_3037_;
                            v_isShared_3147_ = v_isSharedCheck_3151_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3144_);
                            crate::leanh::lean_dec(v___x_3037_);
                            v___x_3146_ = crate::leanh::lean_box(0);
                            v_isShared_3147_ = v_isSharedCheck_3151_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_opts_3033_);
                    crate::leanh::lean_dec_ref(v_env_3028_);
                    crate::leanh::lean_dec_ref(v_x_3023_);
                    v_a_3152_ = crate::leanh::lean_ctor_get(v___x_3034_, 0);
                    v_isSharedCheck_3159_ = (!crate::leanh::lean_is_exclusive(v___x_3034_)) as u8;
                    if v_isSharedCheck_3159_ == 0 {
                        v___x_3154_ = v___x_3034_;
                        v_isShared_3155_ = v_isSharedCheck_3159_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3152_);
                        crate::leanh::lean_dec(v___x_3034_);
                        v___x_3154_ = crate::leanh::lean_box(0);
                        v_isShared_3155_ = v_isSharedCheck_3159_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3054_ = lean_st_ref_get(v___y_3025_);
                v_maxRecDepth_3055_ = crate::leanh::lean_ctor_get(v___x_3054_, 5);
                crate::leanh::lean_inc(v_maxRecDepth_3055_);
                crate::leanh::lean_dec(v___x_3054_);
                v___x_3056_ = lean_st_ref_get(v___y_3025_);
                v_nextMacroScope_3057_ = crate::leanh::lean_ctor_get(v___x_3056_, 4);
                crate::leanh::lean_inc(v_nextMacroScope_3057_);
                crate::leanh::lean_dec(v___x_3056_);
                crate::leanh::lean_inc(v_currRecDepth_3044_);
                v___x_3058_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3058_, 0, v_methods_3051_);
                crate::leanh::lean_ctor_set(v___x_3058_, 1, v_a_3053_);
                crate::leanh::lean_ctor_set(v___x_3058_, 2, v_a_3043_);
                crate::leanh::lean_ctor_set(v___x_3058_, 3, v_currRecDepth_3044_);
                crate::leanh::lean_ctor_set(v___x_3058_, 4, v_maxRecDepth_3055_);
                crate::leanh::lean_ctor_set(v___x_3058_, 5, v_a_3041_);
                v___x_3059_ = crate::leanh::lean_box(0);
                v___x_3060_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3060_, 0, v_nextMacroScope_3057_);
                crate::leanh::lean_ctor_set(v___x_3060_, 1, v___x_3059_);
                crate::leanh::lean_ctor_set(v___x_3060_, 2, v___x_3059_);
                v___x_3061_ = crate::leanh::lean_apply_2(v_x_3023_, v___x_3058_, v___x_3060_);
                if crate::leanh::lean_obj_tag(v___x_3061_) == 0 {
                    v_a_3062_ = crate::leanh::lean_ctor_get(v___x_3061_, 1);
                    crate::leanh::lean_inc(v_a_3062_);
                    v_a_3063_ = crate::leanh::lean_ctor_get(v___x_3061_, 0);
                    crate::leanh::lean_inc(v_a_3063_);
                    crate::leanh::lean_dec_ref_known(v___x_3061_, 2);
                    v_macroScope_3064_ = crate::leanh::lean_ctor_get(v_a_3062_, 0);
                    crate::leanh::lean_inc(v_macroScope_3064_);
                    v_traceMsgs_3065_ = crate::leanh::lean_ctor_get(v_a_3062_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_3065_);
                    v_expandedMacroDecls_3066_ = crate::leanh::lean_ctor_get(v_a_3062_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_3066_);
                    crate::leanh::lean_dec(v_a_3062_);
                    v___x_3067_ = crate::leanh::lean_box(0);
                    v___x_3068_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4___redArg(v_expandedMacroDecls_3066_, v___x_3067_, v___y_3024_, v___y_3025_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_3066_);
                    if crate::leanh::lean_obj_tag(v___x_3068_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3068_, 1);
                        v___x_3069_ = lean_st_ref_take(v___y_3025_);
                        v_env_3070_ = crate::leanh::lean_ctor_get(v___x_3069_, 0);
                        v_messages_3071_ = crate::leanh::lean_ctor_get(v___x_3069_, 1);
                        v_scopes_3072_ = crate::leanh::lean_ctor_get(v___x_3069_, 2);
                        v_usedQuotCtxts_3073_ = crate::leanh::lean_ctor_get(v___x_3069_, 3);
                        v_maxRecDepth_3074_ = crate::leanh::lean_ctor_get(v___x_3069_, 5);
                        v_ngen_3075_ = crate::leanh::lean_ctor_get(v___x_3069_, 6);
                        v_auxDeclNGen_3076_ = crate::leanh::lean_ctor_get(v___x_3069_, 7);
                        v_infoState_3077_ = crate::leanh::lean_ctor_get(v___x_3069_, 8);
                        v_traceState_3078_ = crate::leanh::lean_ctor_get(v___x_3069_, 9);
                        v_snapshotTasks_3079_ = crate::leanh::lean_ctor_get(v___x_3069_, 10);
                        v_isSharedCheck_3105_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3069_)) as u8;
                        if v_isSharedCheck_3105_ == 0 {
                            v_unused_3106_ = crate::leanh::lean_ctor_get(v___x_3069_, 4);
                            crate::leanh::lean_dec(v_unused_3106_);
                            v___x_3081_ = v___x_3069_;
                            v_isShared_3082_ = v_isSharedCheck_3105_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_3079_);
                            crate::leanh::lean_inc(v_traceState_3078_);
                            crate::leanh::lean_inc(v_infoState_3077_);
                            crate::leanh::lean_inc(v_auxDeclNGen_3076_);
                            crate::leanh::lean_inc(v_ngen_3075_);
                            crate::leanh::lean_inc(v_maxRecDepth_3074_);
                            crate::leanh::lean_inc(v_usedQuotCtxts_3073_);
                            crate::leanh::lean_inc(v_scopes_3072_);
                            crate::leanh::lean_inc(v_messages_3071_);
                            crate::leanh::lean_inc(v_env_3070_);
                            crate::leanh::lean_dec(v___x_3069_);
                            v___x_3081_ = crate::leanh::lean_box(0);
                            v_isShared_3082_ = v_isSharedCheck_3105_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_3065_);
                        crate::leanh::lean_dec(v_macroScope_3064_);
                        crate::leanh::lean_dec(v_a_3063_);
                        v_a_3107_ = crate::leanh::lean_ctor_get(v___x_3068_, 0);
                        v_isSharedCheck_3114_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3068_)) as u8;
                        if v_isSharedCheck_3114_ == 0 {
                            v___x_3109_ = v___x_3068_;
                            v_isShared_3110_ = v_isSharedCheck_3114_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3107_);
                            crate::leanh::lean_dec(v___x_3068_);
                            v___x_3109_ = crate::leanh::lean_box(0);
                            v_isShared_3110_ = v_isSharedCheck_3114_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_3115_ = crate::leanh::lean_ctor_get(v___x_3061_, 0);
                    crate::leanh::lean_inc(v_a_3115_);
                    crate::leanh::lean_dec_ref_known(v___x_3061_, 2);
                    if crate::leanh::lean_obj_tag(v_a_3115_) == 0 {
                        v_a_3116_ = crate::leanh::lean_ctor_get(v_a_3115_, 0);
                        crate::leanh::lean_inc(v_a_3116_);
                        v_a_3117_ = crate::leanh::lean_ctor_get(v_a_3115_, 1);
                        crate::leanh::lean_inc_ref(v_a_3117_);
                        crate::leanh::lean_dec_ref_known(v_a_3115_, 2);
                        v___x_3118_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___closed__0;
                        v___x_3119_ = lean_string_dec_eq(v_a_3117_, v___x_3118_);
                        if v___x_3119_ == 0 {
                            v___x_3120_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3120_, 0, v_a_3117_);
                            v___x_3121_ = l_Lean_MessageData_ofFormat(v___x_3120_);
                            v___x_3122_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6___redArg(v_a_3116_, v___x_3121_, v___y_3024_, v___y_3025_);
                            crate::leanh::lean_dec(v_a_3116_);
                            return v___x_3122_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_3117_);
                            v___x_3123_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg(v_a_3116_);
                            return v___x_3123_;
                        }
                    } else {
                        v___x_3124_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                        return v___x_3124_;
                    }
                }
            }
            2 => {
                if v_isShared_3082_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3081_, 4, v_macroScope_3064_);
                    v___x_3084_ = v___x_3081_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3104_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_env_3070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_messages_3071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_scopes_3072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_usedQuotCtxts_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_macroScope_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 5, v_maxRecDepth_3074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_ngen_3075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_auxDeclNGen_3076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_infoState_3077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 9, v_traceState_3078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 10, v_snapshotTasks_3079_);
                    v___x_3084_ = v_reuseFailAlloc_3104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3085_ = lean_st_ref_set(v___y_3025_, v___x_3084_);
                v___x_3086_ = l_List_reverse___redArg(v_traceMsgs_3065_);
                v___x_3087_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__5(v___x_3086_, v___y_3024_, v___y_3025_);
                if crate::leanh::lean_obj_tag(v___x_3087_) == 0 {
                    v_isSharedCheck_3094_ = (!crate::leanh::lean_is_exclusive(v___x_3087_)) as u8;
                    if v_isSharedCheck_3094_ == 0 {
                        v_unused_3095_ = crate::leanh::lean_ctor_get(v___x_3087_, 0);
                        crate::leanh::lean_dec(v_unused_3095_);
                        v___x_3089_ = v___x_3087_;
                        v_isShared_3090_ = v_isSharedCheck_3094_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3087_);
                        v___x_3089_ = crate::leanh::lean_box(0);
                        v_isShared_3090_ = v_isSharedCheck_3094_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3063_);
                    v_a_3096_ = crate::leanh::lean_ctor_get(v___x_3087_, 0);
                    v_isSharedCheck_3103_ = (!crate::leanh::lean_is_exclusive(v___x_3087_)) as u8;
                    if v_isSharedCheck_3103_ == 0 {
                        v___x_3098_ = v___x_3087_;
                        v_isShared_3099_ = v_isSharedCheck_3103_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3096_);
                        crate::leanh::lean_dec(v___x_3087_);
                        v___x_3098_ = crate::leanh::lean_box(0);
                        v_isShared_3099_ = v_isSharedCheck_3103_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_3090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3089_, 0, v_a_3063_);
                    v___x_3092_ = v___x_3089_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3093_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3063_);
                    v___x_3092_ = v_reuseFailAlloc_3093_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3092_;
            }
            6 => {
                if v_isShared_3099_ == 0 {
                    v___x_3101_ = v___x_3098_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
                    v___x_3101_ = v_reuseFailAlloc_3102_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3101_;
            }
            8 => {
                if v_isShared_3110_ == 0 {
                    v___x_3112_ = v___x_3109_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3113_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3113_, 0, v_a_3107_);
                    v___x_3112_ = v_reuseFailAlloc_3113_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3112_;
            }
            10 => {
                if v_isShared_3131_ == 0 {
                    v___x_3133_ = v___x_3130_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
                    v___x_3133_ = v_reuseFailAlloc_3134_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3133_;
            }
            12 => {
                if v_isShared_3139_ == 0 {
                    v___x_3141_ = v___x_3138_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3141_;
            }
            14 => {
                if v_isShared_3147_ == 0 {
                    v___x_3149_ = v___x_3146_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
                    v___x_3149_ = v_reuseFailAlloc_3150_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3149_;
            }
            16 => {
                if v_isShared_3155_ == 0 {
                    v___x_3157_ = v___x_3154_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
                    v___x_3157_ = v_reuseFailAlloc_3158_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg___boxed(
    mut v_x_3160_: *mut crate::leanh::LeanObject,
    mut v___y_3161_: *mut crate::leanh::LeanObject,
    mut v___y_3162_: *mut crate::leanh::LeanObject,
    mut v___y_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3164_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg(
        v_x_3160_,
        v___y_3161_,
        v___y_3162_,
    );
    crate::leanh::lean_dec(v___y_3162_);
    crate::leanh::lean_dec_ref(v___y_3161_);
    return v_res_3164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__3(
    mut v_sz_3165_: usize,
    mut v_i_3166_: usize,
    mut v_bs_3167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3168_: u8 = 0;
    let mut v_v_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: usize = 0;
    let mut v___x_3173_: usize = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3168_ = lean_usize_dec_lt(v_i_3166_, v_sz_3165_);
                if v___x_3168_ == 0 {
                    return v_bs_3167_;
                } else {
                    v_v_3169_ = lean_array_uget(v_bs_3167_, v_i_3166_);
                    v___x_3170_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3171_ = lean_array_uset(v_bs_3167_, v_i_3166_, v___x_3170_);
                    v___x_3172_ = 1usize;
                    v___x_3173_ = lean_usize_add(v_i_3166_, v___x_3172_);
                    v___x_3174_ = lean_array_uset(v_bs_x27_3171_, v_i_3166_, v_v_3169_);
                    v_i_3166_ = v___x_3173_;
                    v_bs_3167_ = v___x_3174_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__3___boxed(
    mut v_sz_3176_: *mut crate::leanh::LeanObject,
    mut v_i_3177_: *mut crate::leanh::LeanObject,
    mut v_bs_3178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3179_: usize = 0;
    let mut v_i_boxed_3180_: usize = 0;
    let mut v_res_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3179_ = crate::leanh::lean_unbox_usize(v_sz_3176_);
    crate::leanh::lean_dec(v_sz_3176_);
    v_i_boxed_3180_ = crate::leanh::lean_unbox_usize(v_i_3177_);
    crate::leanh::lean_dec(v_i_3177_);
    v_res_3181_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__3(v_sz_boxed_3179_, v_i_boxed_3180_, v_bs_3178_);
    return v_res_3181_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__2(
    mut v_sz_3182_: usize,
    mut v_i_3183_: usize,
    mut v_bs_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: usize = 0;
    let mut v___x_3196_: usize = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3202_: u8 = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3188_ = lean_usize_dec_lt(v_i_3183_, v_sz_3182_);
                if v___x_3188_ == 0 {
                    v___x_3189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3189_, 0, v_bs_3184_);
                    return v___x_3189_;
                } else {
                    v_v_3190_ = lean_array_uget_borrowed(v_bs_3184_, v_i_3183_);
                    crate::leanh::lean_inc(v_v_3190_);
                    v___x_3191_ =
                        l_Lean_Elab_Command_expandMacroArg(v_v_3190_, v___y_3185_, v___y_3186_);
                    if crate::leanh::lean_obj_tag(v___x_3191_) == 0 {
                        v_a_3192_ = crate::leanh::lean_ctor_get(v___x_3191_, 0);
                        crate::leanh::lean_inc(v_a_3192_);
                        crate::leanh::lean_dec_ref_known(v___x_3191_, 1);
                        v___x_3193_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3194_ = lean_array_uset(v_bs_3184_, v_i_3183_, v___x_3193_);
                        v___x_3195_ = 1usize;
                        v___x_3196_ = lean_usize_add(v_i_3183_, v___x_3195_);
                        v___x_3197_ = lean_array_uset(v_bs_x27_3194_, v_i_3183_, v_a_3192_);
                        v_i_3183_ = v___x_3196_;
                        v_bs_3184_ = v___x_3197_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3184_);
                        v_a_3199_ = crate::leanh::lean_ctor_get(v___x_3191_, 0);
                        v_isSharedCheck_3206_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3191_)) as u8;
                        if v_isSharedCheck_3206_ == 0 {
                            v___x_3201_ = v___x_3191_;
                            v_isShared_3202_ = v_isSharedCheck_3206_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3199_);
                            crate::leanh::lean_dec(v___x_3191_);
                            v___x_3201_ = crate::leanh::lean_box(0);
                            v_isShared_3202_ = v_isSharedCheck_3206_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3202_ == 0 {
                    v___x_3204_ = v___x_3201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3205_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
                    v___x_3204_ = v_reuseFailAlloc_3205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__2___boxed(
    mut v_sz_3207_: *mut crate::leanh::LeanObject,
    mut v_i_3208_: *mut crate::leanh::LeanObject,
    mut v_bs_3209_: *mut crate::leanh::LeanObject,
    mut v___y_3210_: *mut crate::leanh::LeanObject,
    mut v___y_3211_: *mut crate::leanh::LeanObject,
    mut v___y_3212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3213_: usize = 0;
    let mut v_i_boxed_3214_: usize = 0;
    let mut v_res_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3213_ = crate::leanh::lean_unbox_usize(v_sz_3207_);
    crate::leanh::lean_dec(v_sz_3207_);
    v_i_boxed_3214_ = crate::leanh::lean_unbox_usize(v_i_3208_);
    crate::leanh::lean_dec(v_i_3208_);
    v_res_3215_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__2(v_sz_boxed_3213_, v_i_boxed_3214_, v_bs_3209_, v___y_3210_, v___y_3211_);
    crate::leanh::lean_dec(v___y_3211_);
    crate::leanh::lean_dec_ref(v___y_3210_);
    return v_res_3215_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacro___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = l_Lean_Elab_Command_elabMacro___closed__10;
    v___x_3228_ = l_String_toRawSubstring_x27(v___x_3227_);
    return v___x_3228_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacro___closed__21() -> *mut crate::leanh::LeanObject {
    let mut v___x_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3245_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1___closed__1;
    v___x_3246_ = l_String_toRawSubstring_x27(v___x_3245_);
    return v___x_3246_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacro___closed__34() -> *mut crate::leanh::LeanObject {
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3272_ = l_Lean_Elab_Command_elabMacro___closed__33;
    v___x_3273_ = l_String_toRawSubstring_x27(v___x_3272_);
    return v___x_3273_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabMacro___closed__67() -> *mut crate::leanh::LeanObject {
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3339_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_3339_;
}
pub unsafe fn l_Lean_Elab_Command_elabMacro(
    mut v_x_3367_: *mut crate::leanh::LeanObject,
    mut v_a_3368_: *mut crate::leanh::LeanObject,
    mut v_a_3369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: u8 = 0;
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rulesKind_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: u8 = 0;
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_a_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3639_: u8 = 0;
    let mut v_a_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3643_: u8 = 0;
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v___y_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3689_: u8 = 0;
    let mut v___x_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3693_: u8 = 0;
    let mut v_a_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3697_: u8 = 0;
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v___y_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3719_: u8 = 0;
    let mut v___y_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3734_: u8 = 0;
    let mut v___y_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3741_: usize = 0;
    let mut v___y_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3761_: usize = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v_a_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3792_: u8 = 0;
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3796_: u8 = 0;
    let mut v___y_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3811_: u8 = 0;
    let mut v___y_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3818_: usize = 0;
    let mut v___y_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3853_: u8 = 0;
    let mut v___y_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3859_: usize = 0;
    let mut v___y_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: u8 = 0;
    let mut v___y_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3895_: usize = 0;
    let mut v___y_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3923_: u8 = 0;
    let mut v___y_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3930_: usize = 0;
    let mut v___y_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3948_: u8 = 0;
    let mut v___y_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: u8 = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3974_: u8 = 0;
    let mut v_rhs_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3990_: usize = 0;
    let mut v___x_3991_: usize = 0;
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cat_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: u8 = 0;
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4007_: u8 = 0;
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4011_: u8 = 0;
    let mut v_a_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4015_: u8 = 0;
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4019_: u8 = 0;
    let mut v_a_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4023_: u8 = 0;
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4027_: u8 = 0;
    let mut v_a_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4031_: u8 = 0;
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4035_: u8 = 0;
    let mut v_a_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4039_: u8 = 0;
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4043_: u8 = 0;
    let mut v___y_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4051_: u8 = 0;
    let mut v___y_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: u8 = 0;
    let mut v___x_4062_: u8 = 0;
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: u8 = 0;
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4077_: u8 = 0;
    let mut v___y_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: u8 = 0;
    let mut v___x_4088_: u8 = 0;
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: u8 = 0;
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rulesKind_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: u8 = 0;
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: u8 = 0;
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: u8 = 0;
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: u8 = 0;
    let mut v___x_4130_: u8 = 0;
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: u8 = 0;
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: u8 = 0;
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: u8 = 0;
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3404_ = l_Lean_Elab_Command_elabMacro___closed__0;
                v___x_3405_ = l_Lean_Elab_Command_elabMacro___closed__1;
                v___x_3539_ = l_Lean_Elab_Command_elabMacro___closed__45;
                crate::leanh::lean_inc(v_x_3367_);
                v___x_3540_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3539_);
                if v___x_3540_ == 0 {
                    crate::leanh::lean_dec(v_x_3367_);
                    v___x_3541_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                    return v___x_3541_;
                } else {
                    v___x_3542_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4140_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_3542_);
                    v___x_4141_ = l_Lean_Syntax_isNone(v___x_4140_);
                    if v___x_4141_ == 0 {
                        v___x_4142_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_4140_);
                        v___x_4143_ = l_Lean_Syntax_matchesNull(v___x_4140_, v___x_4142_);
                        if v___x_4143_ == 0 {
                            crate::leanh::lean_dec(v___x_4140_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v___x_4144_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                            return v___x_4144_;
                        } else {
                            v_doc_x3f_4145_ = l_Lean_Syntax_getArg(v___x_4140_, v___x_3542_);
                            crate::leanh::lean_dec(v___x_4140_);
                            v___x_4146_ = l_Lean_Elab_Command_elabMacro___closed__77;
                            crate::leanh::lean_inc(v_doc_x3f_4145_);
                            v___x_4147_ = l_Lean_Syntax_isOfKind(v_doc_x3f_4145_, v___x_4146_);
                            if v___x_4147_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_4145_);
                                crate::leanh::lean_dec(v_x_3367_);
                                v___x_4148_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                                return v___x_4148_;
                            } else {
                                v___x_4149_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4149_, 0, v_doc_x3f_4145_);
                                v_doc_x3f_4124_ = v___x_4149_;
                                v___y_4125_ = v_a_3368_;
                                v___y_4126_ = v_a_3369_;
                                state = 43;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4140_);
                        v___x_4150_ = crate::leanh::lean_box(0);
                        v_doc_x3f_4124_ = v___x_4150_;
                        v___y_4125_ = v_a_3368_;
                        v___y_4126_ = v_a_3369_;
                        state = 43;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v___y_3382_, 3);
                crate::leanh::lean_inc_n(v___y_3383_, 8);
                v___x_3394_ = l_Lean_Syntax_node1(v___y_3383_, v___y_3382_, v___y_3393_);
                crate::leanh::lean_inc(v___y_3389_);
                v___x_3395_ =
                    l_Lean_Syntax_node2(v___y_3383_, v___y_3389_, v___y_3390_, v___x_3394_);
                v___x_3396_ = l_Lean_Syntax_node3(
                    v___y_3383_,
                    v___y_3391_,
                    v___y_3372_,
                    v___x_3395_,
                    v___y_3375_,
                );
                v___x_3397_ =
                    l_Lean_Syntax_node2(v___y_3383_, v___y_3382_, v___x_3396_, v___y_3379_);
                v___x_3398_ =
                    l_Lean_Syntax_node2(v___y_3383_, v___y_3389_, v___y_3392_, v___x_3397_);
                v___x_3399_ = l_Lean_Syntax_node4(
                    v___y_3383_,
                    v___y_3373_,
                    v___y_3374_,
                    v___y_3387_,
                    v___y_3386_,
                    v___x_3398_,
                );
                v___x_3400_ = l_Lean_Syntax_node1(v___y_3383_, v___y_3382_, v___x_3399_);
                v___x_3401_ = l_Lean_Syntax_node1(v___y_3383_, v___y_3377_, v___x_3400_);
                crate::leanh::lean_inc(v___y_3380_);
                crate::leanh::lean_inc(v___y_3378_);
                v___x_3402_ = l_Lean_Syntax_node6(
                    v___y_3383_,
                    v___y_3378_,
                    v___y_3384_,
                    v___y_3380_,
                    v___y_3388_,
                    v___y_3376_,
                    v___y_3380_,
                    v___x_3401_,
                );
                v___x_3403_ =
                    l_Lean_Elab_Command_elabCommand(v___x_3402_, v___y_3381_, v___y_3385_);
                crate::leanh::lean_dec_ref(v___y_3381_);
                return v___x_3403_;
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_3410_, 2);
                v___x_3420_ = l_Array_append___redArg(v___y_3410_, v___y_3419_);
                crate::leanh::lean_dec_ref(v___y_3419_);
                crate::leanh::lean_inc_n(v___y_3411_, 5);
                crate::leanh::lean_inc_n(v___y_3415_, 14);
                v___x_3421_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3421_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3421_, 1, v___y_3411_);
                crate::leanh::lean_ctor_set(v___x_3421_, 2, v___x_3420_);
                v___x_3422_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3422_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3422_, 1, v___y_3411_);
                crate::leanh::lean_ctor_set(v___x_3422_, 2, v___y_3410_);
                crate::leanh::lean_inc_ref(v___y_3418_);
                v___x_3423_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3423_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3423_, 1, v___y_3418_);
                v___x_3424_ = l_Lean_Elab_Command_elabMacro___closed__2;
                crate::leanh::lean_inc_ref_n(v___y_3407_, 3);
                v___x_3425_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3407_, v___x_3424_);
                v___x_3426_ = l_Lean_Elab_Command_elabMacro___closed__3;
                v___x_3427_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3407_, v___x_3426_);
                v___x_3428_ = l_Lean_Elab_Command_elabMacro___closed__4;
                v___x_3429_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3429_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3429_, 1, v___x_3428_);
                v___x_3430_ = l_Lean_Elab_Command_elabMacro___closed__5;
                v___x_3431_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3407_, v___x_3430_);
                v___x_3432_ = l_Lean_Elab_Command_elabMacro___closed__6;
                v___x_3433_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3433_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3433_, 1, v___x_3432_);
                crate::leanh::lean_inc_ref(v___y_3409_);
                v___x_3434_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3434_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3434_, 1, v___y_3409_);
                crate::leanh::lean_inc_ref(v___x_3434_);
                crate::leanh::lean_inc_ref(v___x_3433_);
                crate::leanh::lean_inc(v___x_3431_);
                v___x_3435_ = l_Lean_Syntax_node3(
                    v___y_3415_,
                    v___x_3431_,
                    v___x_3433_,
                    v___y_3408_,
                    v___x_3434_,
                );
                v___x_3436_ = l_Lean_Syntax_node1(v___y_3415_, v___y_3411_, v___x_3435_);
                v___x_3437_ = l_Lean_Syntax_node1(v___y_3415_, v___y_3411_, v___x_3436_);
                v___x_3438_ = l_Lean_Elab_Command_elabMacro___closed__7;
                v___x_3439_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3439_, 0, v___y_3415_);
                crate::leanh::lean_ctor_set(v___x_3439_, 1, v___x_3438_);
                v___x_3440_ = l_Lean_Syntax_node3(
                    v___y_3415_,
                    v___x_3431_,
                    v___x_3433_,
                    v___y_3413_,
                    v___x_3434_,
                );
                v___x_3441_ = l_Lean_Syntax_node4(
                    v___y_3415_,
                    v___x_3427_,
                    v___x_3429_,
                    v___x_3437_,
                    v___x_3439_,
                    v___x_3440_,
                );
                v___x_3442_ = l_Lean_Syntax_node1(v___y_3415_, v___y_3411_, v___x_3441_);
                v___x_3443_ = l_Lean_Syntax_node1(v___y_3415_, v___x_3425_, v___x_3442_);
                crate::leanh::lean_inc_ref(v___x_3422_);
                crate::leanh::lean_inc(v___y_3417_);
                v___x_3444_ = l_Lean_Syntax_node6(
                    v___y_3415_,
                    v___y_3417_,
                    v___x_3421_,
                    v___x_3422_,
                    v___y_3416_,
                    v___x_3423_,
                    v___x_3422_,
                    v___x_3443_,
                );
                v___x_3445_ =
                    l_Lean_Elab_Command_elabCommand(v___x_3444_, v___y_3412_, v___y_3414_);
                crate::leanh::lean_dec_ref(v___y_3412_);
                return v___x_3445_;
            }
            3 => {
                crate::leanh::lean_inc_ref_n(v___y_3457_, 2);
                v___x_3466_ = l_Array_append___redArg(v___y_3457_, v___y_3465_);
                crate::leanh::lean_dec_ref(v___y_3465_);
                crate::leanh::lean_inc_n(v___y_3458_, 4);
                crate::leanh::lean_inc_n(v___y_3460_, 18);
                v___x_3467_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3467_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3467_, 1, v___y_3458_);
                crate::leanh::lean_ctor_set(v___x_3467_, 2, v___x_3466_);
                v___x_3468_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3468_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3468_, 1, v___y_3458_);
                crate::leanh::lean_ctor_set(v___x_3468_, 2, v___y_3457_);
                crate::leanh::lean_inc_ref(v___y_3449_);
                v___x_3469_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3469_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3469_, 1, v___y_3449_);
                v___x_3470_ = l_Lean_Elab_Command_elabMacro___closed__2;
                crate::leanh::lean_inc_ref_n(v___y_3448_, 8);
                v___x_3471_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3470_);
                v___x_3472_ = l_Lean_Elab_Command_elabMacro___closed__3;
                v___x_3473_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3472_);
                v___x_3474_ = l_Lean_Elab_Command_elabMacro___closed__4;
                v___x_3475_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3475_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3475_, 1, v___x_3474_);
                v___x_3476_ = l_Lean_Elab_Command_elabMacro___closed__5;
                v___x_3477_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3476_);
                v___x_3478_ = l_Lean_Elab_Command_elabMacro___closed__6;
                v___x_3479_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3479_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3479_, 1, v___x_3478_);
                crate::leanh::lean_inc_ref(v___y_3456_);
                v___x_3480_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3480_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3480_, 1, v___y_3456_);
                crate::leanh::lean_inc_ref(v___x_3480_);
                v___x_3481_ = l_Lean_Syntax_node3(
                    v___y_3460_,
                    v___x_3477_,
                    v___x_3479_,
                    v___y_3455_,
                    v___x_3480_,
                );
                v___x_3482_ = l_Lean_Syntax_node1(v___y_3460_, v___y_3458_, v___x_3481_);
                v___x_3483_ = l_Lean_Syntax_node1(v___y_3460_, v___y_3458_, v___x_3482_);
                v___x_3484_ = l_Lean_Elab_Command_elabMacro___closed__7;
                v___x_3485_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3485_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3485_, 1, v___x_3484_);
                v___x_3486_ = l_Lean_Elab_Command_elabMacro___closed__9;
                v___x_3487_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3486_);
                v___x_3488_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__11_once),
                    _init_l_Lean_Elab_Command_elabMacro___closed__11,
                );
                v___x_3489_ = l_Lean_Elab_Command_elabMacro___closed__14;
                crate::leanh::lean_inc_n(v___y_3450_, 2);
                crate::leanh::lean_inc_n(v___y_3447_, 2);
                v___x_3490_ = l_Lean_addMacroScope(v___y_3447_, v___x_3489_, v___y_3450_);
                v___x_3491_ = crate::leanh::lean_box(0);
                v___x_3492_ = l_Lean_Elab_Command_elabMacro___closed__16;
                v___x_3493_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3493_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3493_, 1, v___x_3488_);
                crate::leanh::lean_ctor_set(v___x_3493_, 2, v___x_3490_);
                crate::leanh::lean_ctor_set(v___x_3493_, 3, v___x_3492_);
                v___x_3494_ = l_Lean_Elab_Command_elabMacro___closed__17;
                v___x_3495_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3494_);
                v___x_3496_ = l_Lean_Elab_Command_elabMacro___closed__18;
                v___x_3497_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3496_);
                crate::leanh::lean_inc_ref(v___y_3451_);
                v___x_3498_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3498_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3498_, 1, v___y_3451_);
                v___x_3499_ = l_Lean_Elab_Command_elabMacro___closed__20;
                v___x_3500_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__21),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__21_once),
                    _init_l_Lean_Elab_Command_elabMacro___closed__21,
                );
                v___x_3501_ = crate::leanh::lean_box(0);
                v___x_3502_ = l_Lean_addMacroScope(v___y_3447_, v___x_3501_, v___y_3450_);
                v___x_3503_ = l_Lean_Elab_Command_elabMacro___closed__24;
                v___x_3504_ = l_Lean_Elab_Command_elabMacro___closed__26;
                v___x_3505_ = l_Lean_Name_mkStr3(v___x_3404_, v___x_3405_, v___y_3448_);
                v___x_3506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3506_, 0, v___x_3505_);
                v___x_3507_ = l_Lean_Elab_Command_elabMacro___closed__30;
                v___x_3508_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3508_, 0, v___x_3506_);
                crate::leanh::lean_ctor_set(v___x_3508_, 1, v___x_3507_);
                v___x_3509_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3509_, 0, v___x_3504_);
                crate::leanh::lean_ctor_set(v___x_3509_, 1, v___x_3508_);
                v___x_3510_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3503_);
                crate::leanh::lean_ctor_set(v___x_3510_, 1, v___x_3509_);
                v___x_3511_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3511_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3511_, 1, v___x_3500_);
                crate::leanh::lean_ctor_set(v___x_3511_, 2, v___x_3502_);
                crate::leanh::lean_ctor_set(v___x_3511_, 3, v___x_3510_);
                v___x_3512_ = l_Lean_Syntax_node1(v___y_3460_, v___x_3499_, v___x_3511_);
                v___x_3513_ =
                    l_Lean_Syntax_node2(v___y_3460_, v___x_3497_, v___x_3498_, v___x_3512_);
                v___x_3514_ = l_Lean_Elab_Command_elabMacro___closed__31;
                v___x_3515_ =
                    l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3514_);
                v___x_3516_ = l_Lean_Elab_Command_elabMacro___closed__32;
                v___x_3517_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3517_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3517_, 1, v___x_3516_);
                v___x_3518_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__34),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__34_once),
                    _init_l_Lean_Elab_Command_elabMacro___closed__34,
                );
                v___x_3519_ = l_Lean_Elab_Command_elabMacro___closed__37;
                v___x_3520_ = l_Lean_addMacroScope(v___y_3447_, v___x_3519_, v___y_3450_);
                v___x_3521_ = l_Lean_Elab_Command_elabMacro___closed__40;
                v___x_3522_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3522_, 0, v___y_3460_);
                crate::leanh::lean_ctor_set(v___x_3522_, 1, v___x_3518_);
                crate::leanh::lean_ctor_set(v___x_3522_, 2, v___x_3520_);
                crate::leanh::lean_ctor_set(v___x_3522_, 3, v___x_3521_);
                v___x_3523_ =
                    l_Lean_Syntax_node2(v___y_3460_, v___x_3515_, v___x_3517_, v___x_3522_);
                v___x_3524_ = l_Lean_TSyntax_getId(v___y_3464_);
                crate::leanh::lean_dec(v___y_3464_);
                v___x_3525_ = lean_erase_macro_scopes(v___x_3524_);
                crate::leanh::lean_inc(v___x_3525_);
                v___x_3526_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                    v___x_3491_,
                    v___x_3525_,
                );
                if crate::leanh::lean_obj_tag(v___x_3526_) == 0 {
                    v___x_3527_ = l_Lean_quoteNameMk(v___x_3525_);
                    v___y_3372_ = v___x_3513_;
                    v___y_3373_ = v___x_3473_;
                    v___y_3374_ = v___x_3475_;
                    v___y_3375_ = v___x_3480_;
                    v___y_3376_ = v___x_3469_;
                    v___y_3377_ = v___x_3471_;
                    v___y_3378_ = v___y_3453_;
                    v___y_3379_ = v___y_3454_;
                    v___y_3380_ = v___x_3468_;
                    v___y_3381_ = v___y_3459_;
                    v___y_3382_ = v___y_3458_;
                    v___y_3383_ = v___y_3460_;
                    v___y_3384_ = v___x_3467_;
                    v___y_3385_ = v___y_3461_;
                    v___y_3386_ = v___x_3485_;
                    v___y_3387_ = v___x_3483_;
                    v___y_3388_ = v___y_3462_;
                    v___y_3389_ = v___x_3487_;
                    v___y_3390_ = v___x_3523_;
                    v___y_3391_ = v___x_3495_;
                    v___y_3392_ = v___x_3493_;
                    v___y_3393_ = v___x_3527_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3525_);
                    v_val_3528_ = crate::leanh::lean_ctor_get(v___x_3526_, 0);
                    crate::leanh::lean_inc(v_val_3528_);
                    crate::leanh::lean_dec_ref_known(v___x_3526_, 1);
                    v___x_3529_ = l_Lean_Elab_Command_elabMacro___closed__41;
                    crate::leanh::lean_inc_ref(v___y_3448_);
                    v___x_3530_ =
                        l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3448_, v___x_3529_);
                    v___x_3531_ = l_Lean_Elab_Command_elabMacro___closed__42;
                    v___x_3532_ = l_Lean_Elab_Command_elabMacro___closed__43;
                    v___x_3533_ = lean_string_intercalate(v___x_3532_, v_val_3528_);
                    v___x_3534_ = lean_string_append(v___x_3531_, v___x_3533_);
                    crate::leanh::lean_dec_ref(v___x_3533_);
                    crate::leanh::lean_inc_n(v___y_3452_, 2);
                    v___x_3535_ = l_Lean_Syntax_mkNameLit(v___x_3534_, v___y_3452_);
                    v___x_3536_ = lean_mk_empty_array_with_capacity(v___y_3463_);
                    v___x_3537_ = lean_array_push(v___x_3536_, v___x_3535_);
                    v___x_3538_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3538_, 0, v___y_3452_);
                    crate::leanh::lean_ctor_set(v___x_3538_, 1, v___x_3530_);
                    crate::leanh::lean_ctor_set(v___x_3538_, 2, v___x_3537_);
                    v___y_3372_ = v___x_3513_;
                    v___y_3373_ = v___x_3473_;
                    v___y_3374_ = v___x_3475_;
                    v___y_3375_ = v___x_3480_;
                    v___y_3376_ = v___x_3469_;
                    v___y_3377_ = v___x_3471_;
                    v___y_3378_ = v___y_3453_;
                    v___y_3379_ = v___y_3454_;
                    v___y_3380_ = v___x_3468_;
                    v___y_3381_ = v___y_3459_;
                    v___y_3382_ = v___y_3458_;
                    v___y_3383_ = v___y_3460_;
                    v___y_3384_ = v___x_3467_;
                    v___y_3385_ = v___y_3461_;
                    v___y_3386_ = v___x_3485_;
                    v___y_3387_ = v___x_3483_;
                    v___y_3388_ = v___y_3462_;
                    v___y_3389_ = v___x_3487_;
                    v___y_3390_ = v___x_3523_;
                    v___y_3391_ = v___x_3495_;
                    v___y_3392_ = v___x_3493_;
                    v___y_3393_ = v___x_3538_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_3555_ = l_Lean_Elab_Command_elabMacro___closed__46;
                v___x_3556_ = l_Lean_Elab_Command_elabMacro___closed__47;
                if crate::leanh::lean_obj_tag(v___y_3544_) == 1 {
                    v_val_3557_ = crate::leanh::lean_ctor_get(v___y_3544_, 0);
                    crate::leanh::lean_inc(v_val_3557_);
                    crate::leanh::lean_dec_ref_known(v___y_3544_, 1);
                    v___x_3558_ = l_Array_mkArray1___redArg(v_val_3557_);
                    v___y_3407_ = v___y_3546_;
                    v___y_3408_ = v___y_3550_;
                    v___y_3409_ = v___y_3551_;
                    v___y_3410_ = v___y_3554_;
                    v___y_3411_ = v___y_3553_;
                    v___y_3412_ = v___y_3552_;
                    v___y_3413_ = v___y_3545_;
                    v___y_3414_ = v___y_3547_;
                    v___y_3415_ = v___y_3548_;
                    v___y_3416_ = v___y_3549_;
                    v___y_3417_ = v___x_3556_;
                    v___y_3418_ = v___x_3555_;
                    v___y_3419_ = v___x_3558_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3544_);
                    v___x_3559_ = l_Lean_Elab_Command_elabMacro___closed__48;
                    v___y_3407_ = v___y_3546_;
                    v___y_3408_ = v___y_3550_;
                    v___y_3409_ = v___y_3551_;
                    v___y_3410_ = v___y_3554_;
                    v___y_3411_ = v___y_3553_;
                    v___y_3412_ = v___y_3552_;
                    v___y_3413_ = v___y_3545_;
                    v___y_3414_ = v___y_3547_;
                    v___y_3415_ = v___y_3548_;
                    v___y_3416_ = v___y_3549_;
                    v___y_3417_ = v___x_3556_;
                    v___y_3418_ = v___x_3555_;
                    v___y_3419_ = v___x_3559_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v___x_3578_ = l_Lean_Elab_Command_elabMacro___closed__46;
                v___x_3579_ = l_Lean_Elab_Command_elabMacro___closed__47;
                if crate::leanh::lean_obj_tag(v___y_3572_) == 1 {
                    v_val_3580_ = crate::leanh::lean_ctor_get(v___y_3572_, 0);
                    crate::leanh::lean_inc(v_val_3580_);
                    crate::leanh::lean_dec_ref_known(v___y_3572_, 1);
                    v___x_3581_ = l_Array_mkArray1___redArg(v_val_3580_);
                    v___y_3447_ = v_a_3577_;
                    v___y_3448_ = v___y_3561_;
                    v___y_3449_ = v___x_3578_;
                    v___y_3450_ = v___y_3562_;
                    v___y_3451_ = v___y_3563_;
                    v___y_3452_ = v___y_3564_;
                    v___y_3453_ = v___x_3579_;
                    v___y_3454_ = v___y_3565_;
                    v___y_3455_ = v___y_3566_;
                    v___y_3456_ = v___y_3567_;
                    v___y_3457_ = v___y_3568_;
                    v___y_3458_ = v___y_3569_;
                    v___y_3459_ = v___y_3570_;
                    v___y_3460_ = v___y_3571_;
                    v___y_3461_ = v___y_3573_;
                    v___y_3462_ = v___y_3574_;
                    v___y_3463_ = v___y_3576_;
                    v___y_3464_ = v___y_3575_;
                    v___y_3465_ = v___x_3581_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3572_);
                    v___x_3582_ = l_Lean_Elab_Command_elabMacro___closed__48;
                    v___y_3447_ = v_a_3577_;
                    v___y_3448_ = v___y_3561_;
                    v___y_3449_ = v___x_3578_;
                    v___y_3450_ = v___y_3562_;
                    v___y_3451_ = v___y_3563_;
                    v___y_3452_ = v___y_3564_;
                    v___y_3453_ = v___x_3579_;
                    v___y_3454_ = v___y_3565_;
                    v___y_3455_ = v___y_3566_;
                    v___y_3456_ = v___y_3567_;
                    v___y_3457_ = v___y_3568_;
                    v___y_3458_ = v___y_3569_;
                    v___y_3459_ = v___y_3570_;
                    v___y_3460_ = v___y_3571_;
                    v___y_3461_ = v___y_3573_;
                    v___y_3462_ = v___y_3574_;
                    v___y_3463_ = v___y_3576_;
                    v___y_3464_ = v___y_3575_;
                    v___y_3465_ = v___x_3582_;
                    state = 3;
                    continue;
                }
            }
            6 => {
                v___x_3598_ = l_Lean_Syntax_getArgs(v___y_3587_);
                v___x_3599_ = lean_array_get_size(v___x_3598_);
                crate::leanh::lean_dec_ref(v___x_3598_);
                v___x_3600_ = lean_nat_dec_eq(v___x_3599_, v___y_3591_);
                if v___x_3600_ == 0 {
                    crate::leanh::lean_dec(v___y_3589_);
                    v___x_3601_ = l_Lean_Elab_Command_elabMacro___lam__0(v___y_3596_, v___y_3597_);
                    if crate::leanh::lean_obj_tag(v___x_3601_) == 0 {
                        v_a_3602_ = crate::leanh::lean_ctor_get(v___x_3601_, 0);
                        crate::leanh::lean_inc(v_a_3602_);
                        crate::leanh::lean_dec_ref_known(v___x_3601_, 1);
                        v___x_3603_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3596_);
                        if crate::leanh::lean_obj_tag(v___x_3603_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3603_, 1);
                            v_quotContext_x3f_3604_ = crate::leanh::lean_ctor_get(v___y_3596_, 5);
                            v___x_3605_ = l_Lean_Syntax_getArg(v___y_3587_, v___y_3591_);
                            crate::leanh::lean_dec(v___y_3587_);
                            if crate::leanh::lean_obj_tag(v_quotContext_x3f_3604_) == 0 {
                                v___x_3606_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_3597_);
                                crate::leanh::lean_dec_ref(v___x_3606_);
                                v___y_3544_ = v___y_3585_;
                                v___y_3545_ = v___x_3605_;
                                v___y_3546_ = v___y_3584_;
                                v___y_3547_ = v___y_3597_;
                                v___y_3548_ = v_a_3602_;
                                v___y_3549_ = v_rulesKind_3595_;
                                v___y_3550_ = v___y_3590_;
                                v___y_3551_ = v___y_3592_;
                                v___y_3552_ = v___y_3596_;
                                v___y_3553_ = v___y_3594_;
                                v___y_3554_ = v___y_3593_;
                                state = 4;
                                continue;
                            } else {
                                v___y_3544_ = v___y_3585_;
                                v___y_3545_ = v___x_3605_;
                                v___y_3546_ = v___y_3584_;
                                v___y_3547_ = v___y_3597_;
                                v___y_3548_ = v_a_3602_;
                                v___y_3549_ = v_rulesKind_3595_;
                                v___y_3550_ = v___y_3590_;
                                v___y_3551_ = v___y_3592_;
                                v___y_3552_ = v___y_3596_;
                                v___y_3553_ = v___y_3594_;
                                v___y_3554_ = v___y_3593_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3602_);
                            crate::leanh::lean_dec_ref(v___y_3596_);
                            crate::leanh::lean_dec(v_rulesKind_3595_);
                            crate::leanh::lean_dec(v___y_3590_);
                            crate::leanh::lean_dec(v___y_3587_);
                            crate::leanh::lean_dec(v___y_3585_);
                            v_a_3607_ = crate::leanh::lean_ctor_get(v___x_3603_, 0);
                            v_isSharedCheck_3614_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3603_)) as u8;
                            if v_isSharedCheck_3614_ == 0 {
                                v___x_3609_ = v___x_3603_;
                                v_isShared_3610_ = v_isSharedCheck_3614_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3607_);
                                crate::leanh::lean_dec(v___x_3603_);
                                v___x_3609_ = crate::leanh::lean_box(0);
                                v_isShared_3610_ = v_isSharedCheck_3614_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3596_);
                        crate::leanh::lean_dec(v_rulesKind_3595_);
                        crate::leanh::lean_dec(v___y_3590_);
                        crate::leanh::lean_dec(v___y_3587_);
                        crate::leanh::lean_dec(v___y_3585_);
                        v_a_3615_ = crate::leanh::lean_ctor_get(v___x_3601_, 0);
                        v_isSharedCheck_3622_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3601_)) as u8;
                        if v_isSharedCheck_3622_ == 0 {
                            v___x_3617_ = v___x_3601_;
                            v_isShared_3618_ = v_isSharedCheck_3622_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3615_);
                            crate::leanh::lean_dec(v___x_3601_);
                            v___x_3617_ = crate::leanh::lean_box(0);
                            v_isShared_3618_ = v_isSharedCheck_3622_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    v___x_3623_ = l_Lean_Elab_Command_elabMacro___lam__0(v___y_3596_, v___y_3597_);
                    if crate::leanh::lean_obj_tag(v___x_3623_) == 0 {
                        v_a_3624_ = crate::leanh::lean_ctor_get(v___x_3623_, 0);
                        crate::leanh::lean_inc(v_a_3624_);
                        crate::leanh::lean_dec_ref_known(v___x_3623_, 1);
                        v___x_3625_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3596_);
                        if crate::leanh::lean_obj_tag(v___x_3625_) == 0 {
                            v_a_3626_ = crate::leanh::lean_ctor_get(v___x_3625_, 0);
                            crate::leanh::lean_inc(v_a_3626_);
                            crate::leanh::lean_dec_ref_known(v___x_3625_, 1);
                            v_quotContext_x3f_3627_ = crate::leanh::lean_ctor_get(v___y_3596_, 5);
                            v___x_3628_ = l_Lean_Syntax_getArg(v___y_3587_, v___x_3542_);
                            crate::leanh::lean_dec(v___y_3587_);
                            if crate::leanh::lean_obj_tag(v_quotContext_x3f_3627_) == 0 {
                                v___x_3629_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_3597_);
                                v_a_3630_ = crate::leanh::lean_ctor_get(v___x_3629_, 0);
                                crate::leanh::lean_inc(v_a_3630_);
                                crate::leanh::lean_dec_ref(v___x_3629_);
                                v___y_3561_ = v___y_3584_;
                                v___y_3562_ = v_a_3626_;
                                v___y_3563_ = v___y_3586_;
                                v___y_3564_ = v___y_3588_;
                                v___y_3565_ = v___x_3628_;
                                v___y_3566_ = v___y_3590_;
                                v___y_3567_ = v___y_3592_;
                                v___y_3568_ = v___y_3593_;
                                v___y_3569_ = v___y_3594_;
                                v___y_3570_ = v___y_3596_;
                                v___y_3571_ = v_a_3624_;
                                v___y_3572_ = v___y_3585_;
                                v___y_3573_ = v___y_3597_;
                                v___y_3574_ = v_rulesKind_3595_;
                                v___y_3575_ = v___y_3589_;
                                v___y_3576_ = v___y_3591_;
                                v_a_3577_ = v_a_3630_;
                                state = 5;
                                continue;
                            } else {
                                v_val_3631_ =
                                    crate::leanh::lean_ctor_get(v_quotContext_x3f_3627_, 0);
                                crate::leanh::lean_inc(v_val_3631_);
                                v___y_3561_ = v___y_3584_;
                                v___y_3562_ = v_a_3626_;
                                v___y_3563_ = v___y_3586_;
                                v___y_3564_ = v___y_3588_;
                                v___y_3565_ = v___x_3628_;
                                v___y_3566_ = v___y_3590_;
                                v___y_3567_ = v___y_3592_;
                                v___y_3568_ = v___y_3593_;
                                v___y_3569_ = v___y_3594_;
                                v___y_3570_ = v___y_3596_;
                                v___y_3571_ = v_a_3624_;
                                v___y_3572_ = v___y_3585_;
                                v___y_3573_ = v___y_3597_;
                                v___y_3574_ = v_rulesKind_3595_;
                                v___y_3575_ = v___y_3589_;
                                v___y_3576_ = v___y_3591_;
                                v_a_3577_ = v_val_3631_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3624_);
                            crate::leanh::lean_dec_ref(v___y_3596_);
                            crate::leanh::lean_dec(v_rulesKind_3595_);
                            crate::leanh::lean_dec(v___y_3590_);
                            crate::leanh::lean_dec(v___y_3589_);
                            crate::leanh::lean_dec(v___y_3587_);
                            crate::leanh::lean_dec(v___y_3585_);
                            v_a_3632_ = crate::leanh::lean_ctor_get(v___x_3625_, 0);
                            v_isSharedCheck_3639_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3625_)) as u8;
                            if v_isSharedCheck_3639_ == 0 {
                                v___x_3634_ = v___x_3625_;
                                v_isShared_3635_ = v_isSharedCheck_3639_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3632_);
                                crate::leanh::lean_dec(v___x_3625_);
                                v___x_3634_ = crate::leanh::lean_box(0);
                                v_isShared_3635_ = v_isSharedCheck_3639_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_3596_);
                        crate::leanh::lean_dec(v_rulesKind_3595_);
                        crate::leanh::lean_dec(v___y_3590_);
                        crate::leanh::lean_dec(v___y_3589_);
                        crate::leanh::lean_dec(v___y_3587_);
                        crate::leanh::lean_dec(v___y_3585_);
                        v_a_3640_ = crate::leanh::lean_ctor_get(v___x_3623_, 0);
                        v_isSharedCheck_3647_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3623_)) as u8;
                        if v_isSharedCheck_3647_ == 0 {
                            v___x_3642_ = v___x_3623_;
                            v_isShared_3643_ = v_isSharedCheck_3647_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3640_);
                            crate::leanh::lean_dec(v___x_3623_);
                            v___x_3642_ = crate::leanh::lean_box(0);
                            v_isShared_3643_ = v_isSharedCheck_3647_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_3610_ == 0 {
                    v___x_3612_ = v___x_3609_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3612_;
            }
            9 => {
                if v_isShared_3618_ == 0 {
                    v___x_3620_ = v___x_3617_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
                    v___x_3620_ = v_reuseFailAlloc_3621_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3620_;
            }
            11 => {
                if v_isShared_3635_ == 0 {
                    v___x_3637_ = v___x_3634_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
                    v___x_3637_ = v_reuseFailAlloc_3638_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3637_;
            }
            13 => {
                if v_isShared_3643_ == 0 {
                    v___x_3645_ = v___x_3642_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
                    v___x_3645_ = v_reuseFailAlloc_3646_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3645_;
            }
            15 => {
                crate::leanh::lean_inc_ref(v___y_3658_);
                crate::leanh::lean_inc(v___y_3657_);
                crate::leanh::lean_inc(v___y_3660_);
                v___x_3664_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3664_, 0, v___y_3660_);
                crate::leanh::lean_ctor_set(v___x_3664_, 1, v___y_3657_);
                crate::leanh::lean_ctor_set(v___x_3664_, 2, v___y_3658_);
                crate::leanh::lean_inc(v___y_3661_);
                v___x_3665_ = l_Lean_Syntax_node1(v___y_3660_, v___y_3661_, v___x_3664_);
                v___y_3584_ = v___y_3649_;
                v___y_3585_ = v___y_3659_;
                v___y_3586_ = v___y_3651_;
                v___y_3587_ = v___y_3652_;
                v___y_3588_ = v___y_3654_;
                v___y_3589_ = v___y_3663_;
                v___y_3590_ = v___y_3655_;
                v___y_3591_ = v___y_3662_;
                v___y_3592_ = v___y_3656_;
                v___y_3593_ = v___y_3658_;
                v___y_3594_ = v___y_3657_;
                v_rulesKind_3595_ = v___x_3665_;
                v___y_3596_ = v___y_3653_;
                v___y_3597_ = v___y_3650_;
                state = 6;
                continue;
            }
            16 => {
                v___x_3682_ = l_Lean_Elab_Command_elabMacro___lam__0(v___y_3671_, v___y_3668_);
                if crate::leanh::lean_obj_tag(v___x_3682_) == 0 {
                    v_a_3683_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                    crate::leanh::lean_inc(v_a_3683_);
                    crate::leanh::lean_dec_ref_known(v___x_3682_, 1);
                    v___x_3684_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3671_);
                    if crate::leanh::lean_obj_tag(v___x_3684_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3684_, 1);
                        if crate::leanh::lean_obj_tag(v___y_3679_) == 0 {
                            v___x_3685_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_3668_);
                            crate::leanh::lean_dec_ref(v___x_3685_);
                            v___y_3649_ = v___y_3667_;
                            v___y_3650_ = v___y_3668_;
                            v___y_3651_ = v___y_3669_;
                            v___y_3652_ = v___y_3670_;
                            v___y_3653_ = v___y_3671_;
                            v___y_3654_ = v___y_3672_;
                            v___y_3655_ = v___y_3673_;
                            v___y_3656_ = v___y_3674_;
                            v___y_3657_ = v___y_3675_;
                            v___y_3658_ = v___y_3676_;
                            v___y_3659_ = v___y_3677_;
                            v___y_3660_ = v_a_3683_;
                            v___y_3661_ = v___y_3678_;
                            v___y_3662_ = v___y_3681_;
                            v___y_3663_ = v___y_3680_;
                            state = 15;
                            continue;
                        } else {
                            v___y_3649_ = v___y_3667_;
                            v___y_3650_ = v___y_3668_;
                            v___y_3651_ = v___y_3669_;
                            v___y_3652_ = v___y_3670_;
                            v___y_3653_ = v___y_3671_;
                            v___y_3654_ = v___y_3672_;
                            v___y_3655_ = v___y_3673_;
                            v___y_3656_ = v___y_3674_;
                            v___y_3657_ = v___y_3675_;
                            v___y_3658_ = v___y_3676_;
                            v___y_3659_ = v___y_3677_;
                            v___y_3660_ = v_a_3683_;
                            v___y_3661_ = v___y_3678_;
                            v___y_3662_ = v___y_3681_;
                            v___y_3663_ = v___y_3680_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3683_);
                        crate::leanh::lean_dec(v___y_3680_);
                        crate::leanh::lean_dec(v___y_3677_);
                        crate::leanh::lean_dec(v___y_3673_);
                        crate::leanh::lean_dec_ref(v___y_3671_);
                        crate::leanh::lean_dec(v___y_3670_);
                        v_a_3686_ = crate::leanh::lean_ctor_get(v___x_3684_, 0);
                        v_isSharedCheck_3693_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3684_)) as u8;
                        if v_isSharedCheck_3693_ == 0 {
                            v___x_3688_ = v___x_3684_;
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3686_);
                            crate::leanh::lean_dec(v___x_3684_);
                            v___x_3688_ = crate::leanh::lean_box(0);
                            v_isShared_3689_ = v_isSharedCheck_3693_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3680_);
                    crate::leanh::lean_dec(v___y_3677_);
                    crate::leanh::lean_dec(v___y_3673_);
                    crate::leanh::lean_dec_ref(v___y_3671_);
                    crate::leanh::lean_dec(v___y_3670_);
                    v_a_3694_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                    v_isSharedCheck_3701_ = (!crate::leanh::lean_is_exclusive(v___x_3682_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v___x_3696_ = v___x_3682_;
                        v_isShared_3697_ = v_isSharedCheck_3701_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3694_);
                        crate::leanh::lean_dec(v___x_3682_);
                        v___x_3696_ = crate::leanh::lean_box(0);
                        v_isShared_3697_ = v_isSharedCheck_3701_;
                        state = 19;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_3689_ == 0 {
                    v___x_3691_ = v___x_3688_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3692_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
                    v___x_3691_ = v_reuseFailAlloc_3692_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3691_;
            }
            19 => {
                if v_isShared_3697_ == 0 {
                    v___x_3699_ = v___x_3696_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
                    v___x_3699_ = v_reuseFailAlloc_3700_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3699_;
            }
            21 => {
                if v___y_3719_ == 0 {
                    v___y_3584_ = v___y_3704_;
                    v___y_3585_ = v___y_3714_;
                    v___y_3586_ = v___y_3706_;
                    v___y_3587_ = v___y_3707_;
                    v___y_3588_ = v___y_3709_;
                    v___y_3589_ = v___y_3717_;
                    v___y_3590_ = v___y_3710_;
                    v___y_3591_ = v___y_3718_;
                    v___y_3592_ = v___y_3711_;
                    v___y_3593_ = v___y_3713_;
                    v___y_3594_ = v___y_3712_;
                    v_rulesKind_3595_ = v___y_3703_;
                    v___y_3596_ = v___y_3708_;
                    v___y_3597_ = v___y_3705_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3703_);
                    v___y_3667_ = v___y_3704_;
                    v___y_3668_ = v___y_3705_;
                    v___y_3669_ = v___y_3706_;
                    v___y_3670_ = v___y_3707_;
                    v___y_3671_ = v___y_3708_;
                    v___y_3672_ = v___y_3709_;
                    v___y_3673_ = v___y_3710_;
                    v___y_3674_ = v___y_3711_;
                    v___y_3675_ = v___y_3712_;
                    v___y_3676_ = v___y_3713_;
                    v___y_3677_ = v___y_3714_;
                    v___y_3678_ = v___y_3715_;
                    v___y_3679_ = v___y_3716_;
                    v___y_3680_ = v___y_3717_;
                    v___y_3681_ = v___y_3718_;
                    state = 16;
                    continue;
                }
            }
            22 => {
                crate::leanh::lean_inc_ref_n(v___y_3726_, 2);
                v___x_3746_ = l_Array_append___redArg(v___y_3726_, v___y_3745_);
                crate::leanh::lean_dec_ref(v___y_3745_);
                crate::leanh::lean_inc_n(v___y_3737_, 3);
                crate::leanh::lean_inc_n(v___y_3742_, 9);
                v___x_3747_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3747_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3747_, 1, v___y_3737_);
                crate::leanh::lean_ctor_set(v___x_3747_, 2, v___x_3746_);
                v___x_3748_ = l_Lean_Elab_Command_elabMacro___closed__50;
                v___x_3749_ = l_Lean_Elab_Command_elabMacro___closed__51;
                v___x_3750_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3750_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3750_, 1, v___x_3749_);
                v___x_3751_ = l_Lean_Elab_Command_elabMacro___closed__52;
                v___x_3752_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3752_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3752_, 1, v___x_3751_);
                v___x_3753_ = l_Lean_Elab_Command_elabMacro___closed__53;
                v___x_3754_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3754_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3754_, 1, v___x_3753_);
                v___x_3755_ = l_Nat_reprFast(v___y_3729_);
                crate::leanh::lean_inc(v___y_3735_);
                v___x_3756_ = l_Lean_Syntax_mkNumLit(v___x_3755_, v___y_3735_);
                v___x_3757_ = l_Lean_Elab_Command_elabMacro___closed__54;
                v___x_3758_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3758_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3758_, 1, v___x_3757_);
                v___x_3759_ = l_Lean_Syntax_node5(
                    v___y_3742_,
                    v___x_3748_,
                    v___x_3750_,
                    v___x_3752_,
                    v___x_3754_,
                    v___x_3756_,
                    v___x_3758_,
                );
                v___x_3760_ = l_Lean_Syntax_node1(v___y_3742_, v___y_3737_, v___x_3759_);
                v_sz_3761_ = lean_array_size(v___y_3740_);
                v___x_3762_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__3(v_sz_3761_, v___y_3741_, v___y_3740_);
                v___x_3763_ = l_Array_append___redArg(v___y_3726_, v___x_3762_);
                crate::leanh::lean_dec_ref(v___x_3762_);
                v___x_3764_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3764_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3764_, 1, v___y_3737_);
                crate::leanh::lean_ctor_set(v___x_3764_, 2, v___x_3763_);
                v___x_3765_ = l_Lean_Elab_Command_elabMacro___closed__55;
                v___x_3766_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3766_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3766_, 1, v___x_3765_);
                v___x_3767_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_3768_ = lean_mk_empty_array_with_capacity(v___x_3767_);
                v___x_3769_ = lean_array_push(v___x_3768_, v___y_3738_);
                v___x_3770_ = lean_array_push(v___x_3769_, v___y_3736_);
                crate::leanh::lean_inc(v___y_3721_);
                v___x_3771_ = lean_array_push(v___x_3770_, v___y_3721_);
                v___x_3772_ = lean_array_push(v___x_3771_, v___y_3725_);
                v___x_3773_ = lean_array_push(v___x_3772_, v___y_3732_);
                v___x_3774_ = lean_array_push(v___x_3773_, v___x_3747_);
                v___x_3775_ = lean_array_push(v___x_3774_, v___x_3760_);
                v___x_3776_ = lean_array_push(v___x_3775_, v___x_3764_);
                v___x_3777_ = lean_array_push(v___x_3776_, v___x_3766_);
                crate::leanh::lean_inc(v___y_3744_);
                v___x_3778_ = lean_array_push(v___x_3777_, v___y_3744_);
                crate::leanh::lean_inc(v___y_3739_);
                v___x_3779_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3779_, 0, v___y_3742_);
                crate::leanh::lean_ctor_set(v___x_3779_, 1, v___y_3739_);
                crate::leanh::lean_ctor_set(v___x_3779_, 2, v___x_3778_);
                v___x_3780_ = l_Lean_Elab_Command_elabSyntax(v___x_3779_, v___y_3733_, v___y_3723_);
                if crate::leanh::lean_obj_tag(v___x_3780_) == 0 {
                    v_a_3781_ = crate::leanh::lean_ctor_get(v___x_3780_, 0);
                    crate::leanh::lean_inc(v_a_3781_);
                    crate::leanh::lean_dec_ref_known(v___x_3780_, 1);
                    crate::leanh::lean_inc(v___y_3735_);
                    v___x_3782_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3782_, 0, v___y_3735_);
                    crate::leanh::lean_ctor_set(v___x_3782_, 1, v_a_3781_);
                    crate::leanh::lean_ctor_set(v___x_3782_, 2, v___y_3731_);
                    if v___y_3734_ == 0 {
                        v___y_3584_ = v___y_3722_;
                        v___y_3585_ = v___y_3727_;
                        v___y_3586_ = v___x_3749_;
                        v___y_3587_ = v___y_3724_;
                        v___y_3588_ = v___y_3735_;
                        v___y_3589_ = v___y_3744_;
                        v___y_3590_ = v___x_3782_;
                        v___y_3591_ = v___y_3730_;
                        v___y_3592_ = v___x_3757_;
                        v___y_3593_ = v___y_3726_;
                        v___y_3594_ = v___y_3737_;
                        v_rulesKind_3595_ = v___y_3721_;
                        v___y_3596_ = v___y_3733_;
                        v___y_3597_ = v___y_3723_;
                        state = 6;
                        continue;
                    } else {
                        v___x_3783_ = l_Lean_Syntax_getArg(v___y_3721_, v___x_3542_);
                        crate::leanh::lean_inc(v___x_3783_);
                        v___x_3784_ = l_Lean_Syntax_matchesNull(v___x_3783_, v___y_3730_);
                        if v___x_3784_ == 0 {
                            crate::leanh::lean_dec(v___x_3783_);
                            v___y_3703_ = v___y_3721_;
                            v___y_3704_ = v___y_3722_;
                            v___y_3705_ = v___y_3723_;
                            v___y_3706_ = v___x_3749_;
                            v___y_3707_ = v___y_3724_;
                            v___y_3708_ = v___y_3733_;
                            v___y_3709_ = v___y_3735_;
                            v___y_3710_ = v___x_3782_;
                            v___y_3711_ = v___x_3757_;
                            v___y_3712_ = v___y_3737_;
                            v___y_3713_ = v___y_3726_;
                            v___y_3714_ = v___y_3727_;
                            v___y_3715_ = v___y_3728_;
                            v___y_3716_ = v___y_3743_;
                            v___y_3717_ = v___y_3744_;
                            v___y_3718_ = v___y_3730_;
                            v___y_3719_ = v___x_3784_;
                            state = 21;
                            continue;
                        } else {
                            v___x_3785_ = l_Lean_Syntax_getArg(v___x_3783_, v___x_3542_);
                            crate::leanh::lean_dec(v___x_3783_);
                            v___x_3786_ = l_Lean_Elab_Command_elabMacro___closed__56;
                            crate::leanh::lean_inc_ref(v___y_3722_);
                            v___x_3787_ = l_Lean_Name_mkStr4(
                                v___x_3404_,
                                v___x_3405_,
                                v___y_3722_,
                                v___x_3786_,
                            );
                            v___x_3788_ = l_Lean_Syntax_isOfKind(v___x_3785_, v___x_3787_);
                            crate::leanh::lean_dec(v___x_3787_);
                            if v___x_3788_ == 0 {
                                v___y_3703_ = v___y_3721_;
                                v___y_3704_ = v___y_3722_;
                                v___y_3705_ = v___y_3723_;
                                v___y_3706_ = v___x_3749_;
                                v___y_3707_ = v___y_3724_;
                                v___y_3708_ = v___y_3733_;
                                v___y_3709_ = v___y_3735_;
                                v___y_3710_ = v___x_3782_;
                                v___y_3711_ = v___x_3757_;
                                v___y_3712_ = v___y_3737_;
                                v___y_3713_ = v___y_3726_;
                                v___y_3714_ = v___y_3727_;
                                v___y_3715_ = v___y_3728_;
                                v___y_3716_ = v___y_3743_;
                                v___y_3717_ = v___y_3744_;
                                v___y_3718_ = v___y_3730_;
                                v___y_3719_ = v___x_3788_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_3721_);
                                v___y_3667_ = v___y_3722_;
                                v___y_3668_ = v___y_3723_;
                                v___y_3669_ = v___x_3749_;
                                v___y_3670_ = v___y_3724_;
                                v___y_3671_ = v___y_3733_;
                                v___y_3672_ = v___y_3735_;
                                v___y_3673_ = v___x_3782_;
                                v___y_3674_ = v___x_3757_;
                                v___y_3675_ = v___y_3737_;
                                v___y_3676_ = v___y_3726_;
                                v___y_3677_ = v___y_3727_;
                                v___y_3678_ = v___y_3728_;
                                v___y_3679_ = v___y_3743_;
                                v___y_3680_ = v___y_3744_;
                                v___y_3681_ = v___y_3730_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_3744_);
                    crate::leanh::lean_dec_ref(v___y_3733_);
                    crate::leanh::lean_dec_ref(v___y_3731_);
                    crate::leanh::lean_dec(v___y_3727_);
                    crate::leanh::lean_dec(v___y_3724_);
                    crate::leanh::lean_dec(v___y_3721_);
                    v_a_3789_ = crate::leanh::lean_ctor_get(v___x_3780_, 0);
                    v_isSharedCheck_3796_ = (!crate::leanh::lean_is_exclusive(v___x_3780_)) as u8;
                    if v_isSharedCheck_3796_ == 0 {
                        v___x_3791_ = v___x_3780_;
                        v_isShared_3792_ = v_isSharedCheck_3796_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3789_);
                        crate::leanh::lean_dec(v___x_3780_);
                        v___x_3791_ = crate::leanh::lean_box(0);
                        v_isShared_3792_ = v_isSharedCheck_3796_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_3792_ == 0 {
                    v___x_3794_ = v___x_3791_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3795_, 0, v_a_3789_);
                    v___x_3794_ = v_reuseFailAlloc_3795_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3794_;
            }
            25 => {
                crate::leanh::lean_inc_ref(v___y_3803_);
                v___x_3823_ = l_Array_append___redArg(v___y_3803_, v___y_3822_);
                crate::leanh::lean_dec_ref(v___y_3822_);
                crate::leanh::lean_inc(v___y_3814_);
                crate::leanh::lean_inc(v___y_3819_);
                v___x_3824_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3824_, 0, v___y_3819_);
                crate::leanh::lean_ctor_set(v___x_3824_, 1, v___y_3814_);
                crate::leanh::lean_ctor_set(v___x_3824_, 2, v___x_3823_);
                if crate::leanh::lean_obj_tag(v___y_3808_) == 1 {
                    v_val_3825_ = crate::leanh::lean_ctor_get(v___y_3808_, 0);
                    crate::leanh::lean_inc(v_val_3825_);
                    crate::leanh::lean_dec_ref_known(v___y_3808_, 1);
                    v___x_3826_ = l_Lean_Elab_Command_elabMacro___closed__58;
                    v___x_3827_ = l_Lean_Elab_Command_elabMacro___closed__51;
                    crate::leanh::lean_inc_n(v___y_3819_, 5);
                    v___x_3828_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3828_, 0, v___y_3819_);
                    crate::leanh::lean_ctor_set(v___x_3828_, 1, v___x_3827_);
                    v___x_3829_ = l_Lean_Elab_Command_elabMacro___closed__59;
                    v___x_3830_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3830_, 0, v___y_3819_);
                    crate::leanh::lean_ctor_set(v___x_3830_, 1, v___x_3829_);
                    v___x_3831_ = l_Lean_Elab_Command_elabMacro___closed__53;
                    v___x_3832_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3832_, 0, v___y_3819_);
                    crate::leanh::lean_ctor_set(v___x_3832_, 1, v___x_3831_);
                    v___x_3833_ = l_Lean_Elab_Command_elabMacro___closed__54;
                    v___x_3834_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3834_, 0, v___y_3819_);
                    crate::leanh::lean_ctor_set(v___x_3834_, 1, v___x_3833_);
                    v___x_3835_ = l_Lean_Syntax_node5(
                        v___y_3819_,
                        v___x_3826_,
                        v___x_3828_,
                        v___x_3830_,
                        v___x_3832_,
                        v_val_3825_,
                        v___x_3834_,
                    );
                    v___x_3836_ = l_Array_mkArray1___redArg(v___x_3835_);
                    v___y_3721_ = v___y_3798_;
                    v___y_3722_ = v___y_3799_;
                    v___y_3723_ = v___y_3801_;
                    v___y_3724_ = v___y_3800_;
                    v___y_3725_ = v___y_3802_;
                    v___y_3726_ = v___y_3803_;
                    v___y_3727_ = v___y_3804_;
                    v___y_3728_ = v___y_3805_;
                    v___y_3729_ = v___y_3806_;
                    v___y_3730_ = v___y_3807_;
                    v___y_3731_ = v___y_3809_;
                    v___y_3732_ = v___x_3824_;
                    v___y_3733_ = v___y_3810_;
                    v___y_3734_ = v___y_3811_;
                    v___y_3735_ = v___y_3812_;
                    v___y_3736_ = v___y_3813_;
                    v___y_3737_ = v___y_3814_;
                    v___y_3738_ = v___y_3815_;
                    v___y_3739_ = v___y_3816_;
                    v___y_3740_ = v___y_3817_;
                    v___y_3741_ = v___y_3818_;
                    v___y_3742_ = v___y_3819_;
                    v___y_3743_ = v___y_3820_;
                    v___y_3744_ = v___y_3821_;
                    v___y_3745_ = v___x_3836_;
                    state = 22;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3808_);
                    v___x_3837_ = l_Lean_Elab_Command_elabMacro___closed__48;
                    v___y_3721_ = v___y_3798_;
                    v___y_3722_ = v___y_3799_;
                    v___y_3723_ = v___y_3801_;
                    v___y_3724_ = v___y_3800_;
                    v___y_3725_ = v___y_3802_;
                    v___y_3726_ = v___y_3803_;
                    v___y_3727_ = v___y_3804_;
                    v___y_3728_ = v___y_3805_;
                    v___y_3729_ = v___y_3806_;
                    v___y_3730_ = v___y_3807_;
                    v___y_3731_ = v___y_3809_;
                    v___y_3732_ = v___x_3824_;
                    v___y_3733_ = v___y_3810_;
                    v___y_3734_ = v___y_3811_;
                    v___y_3735_ = v___y_3812_;
                    v___y_3736_ = v___y_3813_;
                    v___y_3737_ = v___y_3814_;
                    v___y_3738_ = v___y_3815_;
                    v___y_3739_ = v___y_3816_;
                    v___y_3740_ = v___y_3817_;
                    v___y_3741_ = v___y_3818_;
                    v___y_3742_ = v___y_3819_;
                    v___y_3743_ = v___y_3820_;
                    v___y_3744_ = v___y_3821_;
                    v___y_3745_ = v___x_3837_;
                    state = 22;
                    continue;
                }
            }
            26 => {
                crate::leanh::lean_inc_ref(v___y_3844_);
                v___x_3864_ = l_Array_append___redArg(v___y_3844_, v___y_3863_);
                crate::leanh::lean_dec_ref(v___y_3863_);
                crate::leanh::lean_inc(v___y_3855_);
                crate::leanh::lean_inc_n(v___y_3860_, 2);
                v___x_3865_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3865_, 0, v___y_3860_);
                crate::leanh::lean_ctor_set(v___x_3865_, 1, v___y_3855_);
                crate::leanh::lean_ctor_set(v___x_3865_, 2, v___x_3864_);
                crate::leanh::lean_inc_ref(v___y_3845_);
                v___x_3866_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3866_, 0, v___y_3860_);
                crate::leanh::lean_ctor_set(v___x_3866_, 1, v___y_3845_);
                if crate::leanh::lean_obj_tag(v___y_3843_) == 1 {
                    v_val_3867_ = crate::leanh::lean_ctor_get(v___y_3843_, 0);
                    crate::leanh::lean_inc(v_val_3867_);
                    crate::leanh::lean_dec_ref_known(v___y_3843_, 1);
                    v___x_3868_ = l_Lean_Elab_Command_elabMacro___closed__61;
                    v___x_3869_ = l_Lean_Elab_Command_elabMacro___closed__55;
                    crate::leanh::lean_inc_n(v___y_3860_, 2);
                    v___x_3870_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3870_, 0, v___y_3860_);
                    crate::leanh::lean_ctor_set(v___x_3870_, 1, v___x_3869_);
                    v___x_3871_ =
                        l_Lean_Syntax_node2(v___y_3860_, v___x_3868_, v___x_3870_, v_val_3867_);
                    v___x_3872_ = l_Array_mkArray1___redArg(v___x_3871_);
                    v___y_3798_ = v___y_3839_;
                    v___y_3799_ = v___y_3840_;
                    v___y_3800_ = v___y_3842_;
                    v___y_3801_ = v___y_3841_;
                    v___y_3802_ = v___x_3866_;
                    v___y_3803_ = v___y_3844_;
                    v___y_3804_ = v___y_3846_;
                    v___y_3805_ = v___y_3847_;
                    v___y_3806_ = v___y_3848_;
                    v___y_3807_ = v___y_3849_;
                    v___y_3808_ = v___y_3850_;
                    v___y_3809_ = v___y_3851_;
                    v___y_3810_ = v___y_3852_;
                    v___y_3811_ = v___y_3853_;
                    v___y_3812_ = v___y_3854_;
                    v___y_3813_ = v___x_3865_;
                    v___y_3814_ = v___y_3855_;
                    v___y_3815_ = v___y_3856_;
                    v___y_3816_ = v___y_3857_;
                    v___y_3817_ = v___y_3858_;
                    v___y_3818_ = v___y_3859_;
                    v___y_3819_ = v___y_3860_;
                    v___y_3820_ = v___y_3861_;
                    v___y_3821_ = v___y_3862_;
                    v___y_3822_ = v___x_3872_;
                    state = 25;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3843_);
                    v___x_3873_ = l_Lean_Elab_Command_elabMacro___closed__48;
                    v___y_3798_ = v___y_3839_;
                    v___y_3799_ = v___y_3840_;
                    v___y_3800_ = v___y_3842_;
                    v___y_3801_ = v___y_3841_;
                    v___y_3802_ = v___x_3866_;
                    v___y_3803_ = v___y_3844_;
                    v___y_3804_ = v___y_3846_;
                    v___y_3805_ = v___y_3847_;
                    v___y_3806_ = v___y_3848_;
                    v___y_3807_ = v___y_3849_;
                    v___y_3808_ = v___y_3850_;
                    v___y_3809_ = v___y_3851_;
                    v___y_3810_ = v___y_3852_;
                    v___y_3811_ = v___y_3853_;
                    v___y_3812_ = v___y_3854_;
                    v___y_3813_ = v___x_3865_;
                    v___y_3814_ = v___y_3855_;
                    v___y_3815_ = v___y_3856_;
                    v___y_3816_ = v___y_3857_;
                    v___y_3817_ = v___y_3858_;
                    v___y_3818_ = v___y_3859_;
                    v___y_3819_ = v___y_3860_;
                    v___y_3820_ = v___y_3861_;
                    v___y_3821_ = v___y_3862_;
                    v___y_3822_ = v___x_3873_;
                    state = 25;
                    continue;
                }
            }
            27 => {
                crate::leanh::lean_inc_ref(v___y_3880_);
                v___x_3900_ = l_Array_append___redArg(v___y_3880_, v___y_3899_);
                crate::leanh::lean_dec_ref(v___y_3899_);
                crate::leanh::lean_inc(v___y_3892_);
                crate::leanh::lean_inc(v___y_3896_);
                v___x_3901_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3901_, 0, v___y_3896_);
                crate::leanh::lean_ctor_set(v___x_3901_, 1, v___y_3892_);
                crate::leanh::lean_ctor_set(v___x_3901_, 2, v___x_3900_);
                if crate::leanh::lean_obj_tag(v___y_3890_) == 1 {
                    v_val_3902_ = crate::leanh::lean_ctor_get(v___y_3890_, 0);
                    crate::leanh::lean_inc(v_val_3902_);
                    crate::leanh::lean_dec_ref_known(v___y_3890_, 1);
                    v___x_3903_ = l_Lean_Elab_Command_elabMacro___closed__62;
                    crate::leanh::lean_inc_ref(v___y_3876_);
                    v___x_3904_ =
                        l_Lean_Name_mkStr4(v___x_3404_, v___x_3405_, v___y_3876_, v___x_3903_);
                    v___x_3905_ = l_Lean_Elab_Command_elabMacro___closed__63;
                    crate::leanh::lean_inc_n(v___y_3896_, 4);
                    v___x_3906_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3906_, 0, v___y_3896_);
                    crate::leanh::lean_ctor_set(v___x_3906_, 1, v___x_3905_);
                    crate::leanh::lean_inc_ref(v___y_3880_);
                    v___x_3907_ = l_Array_append___redArg(v___y_3880_, v_val_3902_);
                    crate::leanh::lean_dec(v_val_3902_);
                    crate::leanh::lean_inc(v___y_3892_);
                    v___x_3908_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3908_, 0, v___y_3896_);
                    crate::leanh::lean_ctor_set(v___x_3908_, 1, v___y_3892_);
                    crate::leanh::lean_ctor_set(v___x_3908_, 2, v___x_3907_);
                    v___x_3909_ = l_Lean_Elab_Command_elabMacro___closed__64;
                    v___x_3910_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3910_, 0, v___y_3896_);
                    crate::leanh::lean_ctor_set(v___x_3910_, 1, v___x_3909_);
                    v___x_3911_ = l_Lean_Syntax_node3(
                        v___y_3896_,
                        v___x_3904_,
                        v___x_3906_,
                        v___x_3908_,
                        v___x_3910_,
                    );
                    v___x_3912_ = l_Array_mkArray1___redArg(v___x_3911_);
                    v___y_3839_ = v___y_3875_;
                    v___y_3840_ = v___y_3876_;
                    v___y_3841_ = v___y_3878_;
                    v___y_3842_ = v___y_3877_;
                    v___y_3843_ = v___y_3879_;
                    v___y_3844_ = v___y_3880_;
                    v___y_3845_ = v___y_3881_;
                    v___y_3846_ = v___y_3882_;
                    v___y_3847_ = v___y_3883_;
                    v___y_3848_ = v___y_3884_;
                    v___y_3849_ = v___y_3885_;
                    v___y_3850_ = v___y_3886_;
                    v___y_3851_ = v___y_3887_;
                    v___y_3852_ = v___y_3888_;
                    v___y_3853_ = v___y_3889_;
                    v___y_3854_ = v___y_3891_;
                    v___y_3855_ = v___y_3892_;
                    v___y_3856_ = v___x_3901_;
                    v___y_3857_ = v___y_3893_;
                    v___y_3858_ = v___y_3894_;
                    v___y_3859_ = v___y_3895_;
                    v___y_3860_ = v___y_3896_;
                    v___y_3861_ = v___y_3897_;
                    v___y_3862_ = v___y_3898_;
                    v___y_3863_ = v___x_3912_;
                    state = 26;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_3890_);
                    v___x_3913_ = l_Lean_Elab_Command_elabMacro___closed__48;
                    v___y_3839_ = v___y_3875_;
                    v___y_3840_ = v___y_3876_;
                    v___y_3841_ = v___y_3878_;
                    v___y_3842_ = v___y_3877_;
                    v___y_3843_ = v___y_3879_;
                    v___y_3844_ = v___y_3880_;
                    v___y_3845_ = v___y_3881_;
                    v___y_3846_ = v___y_3882_;
                    v___y_3847_ = v___y_3883_;
                    v___y_3848_ = v___y_3884_;
                    v___y_3849_ = v___y_3885_;
                    v___y_3850_ = v___y_3886_;
                    v___y_3851_ = v___y_3887_;
                    v___y_3852_ = v___y_3888_;
                    v___y_3853_ = v___y_3889_;
                    v___y_3854_ = v___y_3891_;
                    v___y_3855_ = v___y_3892_;
                    v___y_3856_ = v___x_3901_;
                    v___y_3857_ = v___y_3893_;
                    v___y_3858_ = v___y_3894_;
                    v___y_3859_ = v___y_3895_;
                    v___y_3860_ = v___y_3896_;
                    v___y_3861_ = v___y_3897_;
                    v___y_3862_ = v___y_3898_;
                    v___y_3863_ = v___x_3913_;
                    state = 26;
                    continue;
                }
            }
            28 => {
                v___x_3936_ = l_Lean_Elab_Command_elabMacro___closed__65;
                v___x_3937_ = l_Lean_Elab_Command_elabMacro___closed__66;
                v___x_3938_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__67),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabMacro___closed__67_once),
                    _init_l_Lean_Elab_Command_elabMacro___closed__67,
                );
                if crate::leanh::lean_obj_tag(v___y_3926_) == 1 {
                    v_val_3939_ = crate::leanh::lean_ctor_get(v___y_3926_, 0);
                    crate::leanh::lean_inc(v_val_3939_);
                    v___x_3940_ = l_Array_mkArray1___redArg(v_val_3939_);
                    v___y_3875_ = v___y_3915_;
                    v___y_3876_ = v___y_3917_;
                    v___y_3877_ = v___y_3918_;
                    v___y_3878_ = v___y_3919_;
                    v___y_3879_ = v___y_3922_;
                    v___y_3880_ = v___x_3938_;
                    v___y_3881_ = v___x_3936_;
                    v___y_3882_ = v___y_3926_;
                    v___y_3883_ = v___y_3928_;
                    v___y_3884_ = v___y_3929_;
                    v___y_3885_ = v___y_3934_;
                    v___y_3886_ = v___y_3935_;
                    v___y_3887_ = v___y_3916_;
                    v___y_3888_ = v___y_3920_;
                    v___y_3889_ = v___y_3923_;
                    v___y_3890_ = v___y_3921_;
                    v___y_3891_ = v___y_3924_;
                    v___y_3892_ = v___y_3925_;
                    v___y_3893_ = v___x_3937_;
                    v___y_3894_ = v___y_3927_;
                    v___y_3895_ = v___y_3930_;
                    v___y_3896_ = v___y_3932_;
                    v___y_3897_ = v___y_3931_;
                    v___y_3898_ = v___y_3933_;
                    v___y_3899_ = v___x_3940_;
                    state = 27;
                    continue;
                } else {
                    v___x_3941_ = l_Lean_Elab_Command_elabMacro___closed__48;
                    v___y_3875_ = v___y_3915_;
                    v___y_3876_ = v___y_3917_;
                    v___y_3877_ = v___y_3918_;
                    v___y_3878_ = v___y_3919_;
                    v___y_3879_ = v___y_3922_;
                    v___y_3880_ = v___x_3938_;
                    v___y_3881_ = v___x_3936_;
                    v___y_3882_ = v___y_3926_;
                    v___y_3883_ = v___y_3928_;
                    v___y_3884_ = v___y_3929_;
                    v___y_3885_ = v___y_3934_;
                    v___y_3886_ = v___y_3935_;
                    v___y_3887_ = v___y_3916_;
                    v___y_3888_ = v___y_3920_;
                    v___y_3889_ = v___y_3923_;
                    v___y_3890_ = v___y_3921_;
                    v___y_3891_ = v___y_3924_;
                    v___y_3892_ = v___y_3925_;
                    v___y_3893_ = v___x_3937_;
                    v___y_3894_ = v___y_3927_;
                    v___y_3895_ = v___y_3930_;
                    v___y_3896_ = v___y_3932_;
                    v___y_3897_ = v___y_3931_;
                    v___y_3898_ = v___y_3933_;
                    v___y_3899_ = v___x_3941_;
                    state = 27;
                    continue;
                }
            }
            29 => {
                v___x_3958_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_3959_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_3958_);
                v___x_3960_ = l_Lean_Elab_Command_elabMacro___closed__69;
                crate::leanh::lean_inc(v___x_3959_);
                v___x_3961_ = l_Lean_Syntax_isOfKind(v___x_3959_, v___x_3960_);
                if v___x_3961_ == 0 {
                    crate::leanh::lean_dec(v___x_3959_);
                    crate::leanh::lean_dec(v_prio_x3f_3955_);
                    crate::leanh::lean_dec(v___y_3953_);
                    crate::leanh::lean_dec(v___y_3950_);
                    crate::leanh::lean_dec(v___y_3949_);
                    crate::leanh::lean_dec(v___y_3946_);
                    crate::leanh::lean_dec(v___y_3944_);
                    crate::leanh::lean_dec(v___y_3943_);
                    crate::leanh::lean_dec(v_x_3367_);
                    v___x_3962_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                    return v___x_3962_;
                } else {
                    v___x_3963_ = l_Lean_Elab_Command_getRef___redArg(v___y_3956_);
                    if crate::leanh::lean_obj_tag(v___x_3963_) == 0 {
                        v_a_3964_ = crate::leanh::lean_ctor_get(v___x_3963_, 0);
                        crate::leanh::lean_inc(v_a_3964_);
                        crate::leanh::lean_dec_ref_known(v___x_3963_, 1);
                        v_fileName_3965_ = crate::leanh::lean_ctor_get(v___y_3956_, 0);
                        v_fileMap_3966_ = crate::leanh::lean_ctor_get(v___y_3956_, 1);
                        v_currRecDepth_3967_ = crate::leanh::lean_ctor_get(v___y_3956_, 2);
                        v_cmdPos_3968_ = crate::leanh::lean_ctor_get(v___y_3956_, 3);
                        v_macroStack_3969_ = crate::leanh::lean_ctor_get(v___y_3956_, 4);
                        v_quotContext_x3f_3970_ = crate::leanh::lean_ctor_get(v___y_3956_, 5);
                        v_currMacroScope_3971_ = crate::leanh::lean_ctor_get(v___y_3956_, 6);
                        v_snap_x3f_3972_ = crate::leanh::lean_ctor_get(v___y_3956_, 8);
                        v_cancelTk_x3f_3973_ = crate::leanh::lean_ctor_get(v___y_3956_, 9);
                        v_suppressElabErrors_3974_ = crate::leanh::lean_ctor_get_uint8(
                            v___y_3956_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        );
                        v_rhs_3975_ = l_Lean_Syntax_getArg(v___x_3959_, v___y_3951_);
                        v___x_3976_ = lean_mk_empty_array_with_capacity(v___y_3954_);
                        v___x_3977_ = lean_array_push(v___x_3976_, v___y_3946_);
                        crate::leanh::lean_inc(v_rhs_3975_);
                        v___x_3978_ = lean_array_push(v___x_3977_, v_rhs_3975_);
                        v___x_3979_ = l_Lean_Elab_Command_elabMacro___closed__71;
                        v___x_3980_ = crate::leanh::lean_box(2);
                        v___x_3981_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3981_, 0, v___x_3980_);
                        crate::leanh::lean_ctor_set(v___x_3981_, 1, v___x_3979_);
                        crate::leanh::lean_ctor_set(v___x_3981_, 2, v___x_3978_);
                        v___x_3982_ = crate::leanh::lean_alloc_closure(
                            l_Lean_evalOptPrio___boxed as *mut core::ffi::c_void,
                            3,
                            1,
                        );
                        crate::leanh::lean_closure_set(v___x_3982_, 0, v_prio_x3f_3955_);
                        v_ref_3983_ = l_Lean_replaceRef(v___x_3981_, v_a_3964_);
                        crate::leanh::lean_dec(v_a_3964_);
                        crate::leanh::lean_dec_ref_known(v___x_3981_, 3);
                        crate::leanh::lean_inc(v_cancelTk_x3f_3973_);
                        crate::leanh::lean_inc(v_snap_x3f_3972_);
                        crate::leanh::lean_inc(v_currMacroScope_3971_);
                        crate::leanh::lean_inc(v_quotContext_x3f_3970_);
                        crate::leanh::lean_inc(v_macroStack_3969_);
                        crate::leanh::lean_inc(v_cmdPos_3968_);
                        crate::leanh::lean_inc(v_currRecDepth_3967_);
                        crate::leanh::lean_inc_ref(v_fileMap_3966_);
                        crate::leanh::lean_inc_ref(v_fileName_3965_);
                        v___x_3984_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_3984_, 0, v_fileName_3965_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 1, v_fileMap_3966_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 2, v_currRecDepth_3967_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 3, v_cmdPos_3968_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 4, v_macroStack_3969_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 5, v_quotContext_x3f_3970_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 6, v_currMacroScope_3971_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 7, v_ref_3983_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 8, v_snap_x3f_3972_);
                        crate::leanh::lean_ctor_set(v___x_3984_, 9, v_cancelTk_x3f_3973_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_3984_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                            v_suppressElabErrors_3974_,
                        );
                        v___x_3985_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg(v___x_3982_, v___x_3984_, v___y_3957_);
                        if crate::leanh::lean_obj_tag(v___x_3985_) == 0 {
                            v_a_3986_ = crate::leanh::lean_ctor_get(v___x_3985_, 0);
                            crate::leanh::lean_inc(v_a_3986_);
                            crate::leanh::lean_dec_ref_known(v___x_3985_, 1);
                            v___x_3987_ = crate::leanh::lean_unsigned_to_nat(7);
                            v___x_3988_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_3987_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v_args_3989_ = l_Lean_Syntax_getArgs(v___x_3988_);
                            crate::leanh::lean_dec(v___x_3988_);
                            v_sz_3990_ = lean_array_size(v_args_3989_);
                            v___x_3991_ = 0usize;
                            v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabMacro_spec__2(v_sz_3990_, v___x_3991_, v_args_3989_, v___x_3984_, v___y_3957_);
                            if crate::leanh::lean_obj_tag(v___x_3992_) == 0 {
                                v_a_3993_ = crate::leanh::lean_ctor_get(v___x_3992_, 0);
                                crate::leanh::lean_inc(v_a_3993_);
                                crate::leanh::lean_dec_ref_known(v___x_3992_, 1);
                                v___x_3994_ = l_Array_unzip___redArg(v_a_3993_);
                                crate::leanh::lean_dec(v_a_3993_);
                                v_fst_3995_ = crate::leanh::lean_ctor_get(v___x_3994_, 0);
                                crate::leanh::lean_inc(v_fst_3995_);
                                v_snd_3996_ = crate::leanh::lean_ctor_get(v___x_3994_, 1);
                                crate::leanh::lean_inc(v_snd_3996_);
                                crate::leanh::lean_dec_ref(v___x_3994_);
                                v___x_3997_ = l_Lean_Elab_Command_getRef___redArg(v___x_3984_);
                                if crate::leanh::lean_obj_tag(v___x_3997_) == 0 {
                                    v_a_3998_ = crate::leanh::lean_ctor_get(v___x_3997_, 0);
                                    crate::leanh::lean_inc(v_a_3998_);
                                    crate::leanh::lean_dec_ref_known(v___x_3997_, 1);
                                    v___x_3999_ =
                                        l_Lean_Elab_Command_getCurrMacroScope___redArg(v___x_3984_);
                                    if crate::leanh::lean_obj_tag(v___x_3999_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3999_, 1);
                                        v_cat_4000_ =
                                            l_Lean_Syntax_getArg(v___x_3959_, v___y_3952_);
                                        crate::leanh::lean_dec(v___x_3959_);
                                        v___x_4001_ = 0;
                                        v___x_4002_ =
                                            l_Lean_SourceInfo_fromRef(v_a_3998_, v___x_4001_);
                                        crate::leanh::lean_dec(v_a_3998_);
                                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_3970_) == 0
                                        {
                                            v___x_4003_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabMacro_spec__4___redArg(v___y_3957_);
                                            crate::leanh::lean_dec_ref(v___x_4003_);
                                            v___y_3915_ = v___y_3943_;
                                            v___y_3916_ = v_snd_3996_;
                                            v___y_3917_ = v___y_3945_;
                                            v___y_3918_ = v_rhs_3975_;
                                            v___y_3919_ = v___y_3957_;
                                            v___y_3920_ = v___x_3984_;
                                            v___y_3921_ = v___y_3950_;
                                            v___y_3922_ = v___y_3949_;
                                            v___y_3923_ = v___y_3948_;
                                            v___y_3924_ = v___x_3980_;
                                            v___y_3925_ = v___x_3979_;
                                            v___y_3926_ = v___y_3944_;
                                            v___y_3927_ = v_fst_3995_;
                                            v___y_3928_ = v___y_3947_;
                                            v___y_3929_ = v_a_3986_;
                                            v___y_3930_ = v___x_3991_;
                                            v___y_3931_ = v_quotContext_x3f_3970_;
                                            v___y_3932_ = v___x_4002_;
                                            v___y_3933_ = v_cat_4000_;
                                            v___y_3934_ = v___y_3952_;
                                            v___y_3935_ = v___y_3953_;
                                            state = 28;
                                            continue;
                                        } else {
                                            v___y_3915_ = v___y_3943_;
                                            v___y_3916_ = v_snd_3996_;
                                            v___y_3917_ = v___y_3945_;
                                            v___y_3918_ = v_rhs_3975_;
                                            v___y_3919_ = v___y_3957_;
                                            v___y_3920_ = v___x_3984_;
                                            v___y_3921_ = v___y_3950_;
                                            v___y_3922_ = v___y_3949_;
                                            v___y_3923_ = v___y_3948_;
                                            v___y_3924_ = v___x_3980_;
                                            v___y_3925_ = v___x_3979_;
                                            v___y_3926_ = v___y_3944_;
                                            v___y_3927_ = v_fst_3995_;
                                            v___y_3928_ = v___y_3947_;
                                            v___y_3929_ = v_a_3986_;
                                            v___y_3930_ = v___x_3991_;
                                            v___y_3931_ = v_quotContext_x3f_3970_;
                                            v___y_3932_ = v___x_4002_;
                                            v___y_3933_ = v_cat_4000_;
                                            v___y_3934_ = v___y_3952_;
                                            v___y_3935_ = v___y_3953_;
                                            state = 28;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_3998_);
                                        crate::leanh::lean_dec(v_snd_3996_);
                                        crate::leanh::lean_dec(v_fst_3995_);
                                        crate::leanh::lean_dec(v_a_3986_);
                                        crate::leanh::lean_dec_ref_known(v___x_3984_, 10);
                                        crate::leanh::lean_dec(v_rhs_3975_);
                                        crate::leanh::lean_dec(v___x_3959_);
                                        crate::leanh::lean_dec(v___y_3953_);
                                        crate::leanh::lean_dec(v___y_3950_);
                                        crate::leanh::lean_dec(v___y_3949_);
                                        crate::leanh::lean_dec(v___y_3944_);
                                        crate::leanh::lean_dec(v___y_3943_);
                                        v_a_4004_ = crate::leanh::lean_ctor_get(v___x_3999_, 0);
                                        v_isSharedCheck_4011_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3999_)) as u8;
                                        if v_isSharedCheck_4011_ == 0 {
                                            v___x_4006_ = v___x_3999_;
                                            v_isShared_4007_ = v_isSharedCheck_4011_;
                                            state = 30;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4004_);
                                            crate::leanh::lean_dec(v___x_3999_);
                                            v___x_4006_ = crate::leanh::lean_box(0);
                                            v_isShared_4007_ = v_isSharedCheck_4011_;
                                            state = 30;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_snd_3996_);
                                    crate::leanh::lean_dec(v_fst_3995_);
                                    crate::leanh::lean_dec(v_a_3986_);
                                    crate::leanh::lean_dec_ref_known(v___x_3984_, 10);
                                    crate::leanh::lean_dec(v_rhs_3975_);
                                    crate::leanh::lean_dec(v___x_3959_);
                                    crate::leanh::lean_dec(v___y_3953_);
                                    crate::leanh::lean_dec(v___y_3950_);
                                    crate::leanh::lean_dec(v___y_3949_);
                                    crate::leanh::lean_dec(v___y_3944_);
                                    crate::leanh::lean_dec(v___y_3943_);
                                    v_a_4012_ = crate::leanh::lean_ctor_get(v___x_3997_, 0);
                                    v_isSharedCheck_4019_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3997_)) as u8;
                                    if v_isSharedCheck_4019_ == 0 {
                                        v___x_4014_ = v___x_3997_;
                                        v_isShared_4015_ = v_isSharedCheck_4019_;
                                        state = 32;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4012_);
                                        crate::leanh::lean_dec(v___x_3997_);
                                        v___x_4014_ = crate::leanh::lean_box(0);
                                        v_isShared_4015_ = v_isSharedCheck_4019_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_3986_);
                                crate::leanh::lean_dec_ref_known(v___x_3984_, 10);
                                crate::leanh::lean_dec(v_rhs_3975_);
                                crate::leanh::lean_dec(v___x_3959_);
                                crate::leanh::lean_dec(v___y_3953_);
                                crate::leanh::lean_dec(v___y_3950_);
                                crate::leanh::lean_dec(v___y_3949_);
                                crate::leanh::lean_dec(v___y_3944_);
                                crate::leanh::lean_dec(v___y_3943_);
                                v_a_4020_ = crate::leanh::lean_ctor_get(v___x_3992_, 0);
                                v_isSharedCheck_4027_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3992_)) as u8;
                                if v_isSharedCheck_4027_ == 0 {
                                    v___x_4022_ = v___x_3992_;
                                    v_isShared_4023_ = v_isSharedCheck_4027_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4020_);
                                    crate::leanh::lean_dec(v___x_3992_);
                                    v___x_4022_ = crate::leanh::lean_box(0);
                                    v_isShared_4023_ = v_isSharedCheck_4027_;
                                    state = 34;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3984_, 10);
                            crate::leanh::lean_dec(v_rhs_3975_);
                            crate::leanh::lean_dec(v___x_3959_);
                            crate::leanh::lean_dec(v___y_3953_);
                            crate::leanh::lean_dec(v___y_3950_);
                            crate::leanh::lean_dec(v___y_3949_);
                            crate::leanh::lean_dec(v___y_3944_);
                            crate::leanh::lean_dec(v___y_3943_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v_a_4028_ = crate::leanh::lean_ctor_get(v___x_3985_, 0);
                            v_isSharedCheck_4035_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3985_)) as u8;
                            if v_isSharedCheck_4035_ == 0 {
                                v___x_4030_ = v___x_3985_;
                                v_isShared_4031_ = v_isSharedCheck_4035_;
                                state = 36;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4028_);
                                crate::leanh::lean_dec(v___x_3985_);
                                v___x_4030_ = crate::leanh::lean_box(0);
                                v_isShared_4031_ = v_isSharedCheck_4035_;
                                state = 36;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3959_);
                        crate::leanh::lean_dec(v_prio_x3f_3955_);
                        crate::leanh::lean_dec(v___y_3953_);
                        crate::leanh::lean_dec(v___y_3950_);
                        crate::leanh::lean_dec(v___y_3949_);
                        crate::leanh::lean_dec(v___y_3946_);
                        crate::leanh::lean_dec(v___y_3944_);
                        crate::leanh::lean_dec(v___y_3943_);
                        crate::leanh::lean_dec(v_x_3367_);
                        v_a_4036_ = crate::leanh::lean_ctor_get(v___x_3963_, 0);
                        v_isSharedCheck_4043_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3963_)) as u8;
                        if v_isSharedCheck_4043_ == 0 {
                            v___x_4038_ = v___x_3963_;
                            v_isShared_4039_ = v_isSharedCheck_4043_;
                            state = 38;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4036_);
                            crate::leanh::lean_dec(v___x_3963_);
                            v___x_4038_ = crate::leanh::lean_box(0);
                            v_isShared_4039_ = v_isSharedCheck_4043_;
                            state = 38;
                            continue;
                        }
                    }
                }
            }
            30 => {
                if v_isShared_4007_ == 0 {
                    v___x_4009_ = v___x_4006_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_4004_);
                    v___x_4009_ = v_reuseFailAlloc_4010_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4009_;
            }
            32 => {
                if v_isShared_4015_ == 0 {
                    v___x_4017_ = v___x_4014_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
                    v___x_4017_ = v_reuseFailAlloc_4018_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4017_;
            }
            34 => {
                if v_isShared_4023_ == 0 {
                    v___x_4025_ = v___x_4022_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4026_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
                    v___x_4025_ = v_reuseFailAlloc_4026_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4025_;
            }
            36 => {
                if v_isShared_4031_ == 0 {
                    v___x_4033_ = v___x_4030_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4034_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4034_, 0, v_a_4028_);
                    v___x_4033_ = v_reuseFailAlloc_4034_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4033_;
            }
            38 => {
                if v_isShared_4039_ == 0 {
                    v___x_4041_ = v___x_4038_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4042_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
                    v___x_4041_ = v_reuseFailAlloc_4042_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4041_;
            }
            40 => {
                v___x_4059_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_4060_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_4059_);
                v___x_4061_ = l_Lean_Syntax_isNone(v___x_4060_);
                if v___x_4061_ == 0 {
                    crate::leanh::lean_inc(v___x_4060_);
                    v___x_4062_ = l_Lean_Syntax_matchesNull(v___x_4060_, v___y_4054_);
                    if v___x_4062_ == 0 {
                        crate::leanh::lean_dec(v___x_4060_);
                        crate::leanh::lean_dec(v_name_x3f_4056_);
                        crate::leanh::lean_dec(v___y_4050_);
                        crate::leanh::lean_dec(v___y_4049_);
                        crate::leanh::lean_dec(v___y_4048_);
                        crate::leanh::lean_dec(v___y_4046_);
                        crate::leanh::lean_dec(v___y_4045_);
                        crate::leanh::lean_dec(v_x_3367_);
                        v___x_4063_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                        return v___x_4063_;
                    } else {
                        v___x_4064_ = l_Lean_Syntax_getArg(v___x_4060_, v___x_3542_);
                        crate::leanh::lean_dec(v___x_4060_);
                        v___x_4065_ = l_Lean_Elab_Command_elabMacro___closed__50;
                        crate::leanh::lean_inc(v___x_4064_);
                        v___x_4066_ = l_Lean_Syntax_isOfKind(v___x_4064_, v___x_4065_);
                        if v___x_4066_ == 0 {
                            crate::leanh::lean_dec(v___x_4064_);
                            crate::leanh::lean_dec(v_name_x3f_4056_);
                            crate::leanh::lean_dec(v___y_4050_);
                            crate::leanh::lean_dec(v___y_4049_);
                            crate::leanh::lean_dec(v___y_4048_);
                            crate::leanh::lean_dec(v___y_4046_);
                            crate::leanh::lean_dec(v___y_4045_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v___x_4067_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                            return v___x_4067_;
                        } else {
                            v_prio_x3f_4068_ = l_Lean_Syntax_getArg(v___x_4064_, v___y_4053_);
                            crate::leanh::lean_dec(v___x_4064_);
                            v___x_4069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4069_, 0, v_prio_x3f_4068_);
                            v___y_3943_ = v___y_4045_;
                            v___y_3944_ = v___y_4048_;
                            v___y_3945_ = v___y_4047_;
                            v___y_3946_ = v___y_4046_;
                            v___y_3947_ = v___y_4052_;
                            v___y_3948_ = v___y_4051_;
                            v___y_3949_ = v___y_4050_;
                            v___y_3950_ = v___y_4049_;
                            v___y_3951_ = v___y_4053_;
                            v___y_3952_ = v___y_4054_;
                            v___y_3953_ = v_name_x3f_4056_;
                            v___y_3954_ = v___y_4055_;
                            v_prio_x3f_3955_ = v___x_4069_;
                            v___y_3956_ = v___y_4057_;
                            v___y_3957_ = v___y_4058_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4060_);
                    v___x_4070_ = crate::leanh::lean_box(0);
                    v___y_3943_ = v___y_4045_;
                    v___y_3944_ = v___y_4048_;
                    v___y_3945_ = v___y_4047_;
                    v___y_3946_ = v___y_4046_;
                    v___y_3947_ = v___y_4052_;
                    v___y_3948_ = v___y_4051_;
                    v___y_3949_ = v___y_4050_;
                    v___y_3950_ = v___y_4049_;
                    v___y_3951_ = v___y_4053_;
                    v___y_3952_ = v___y_4054_;
                    v___y_3953_ = v_name_x3f_4056_;
                    v___y_3954_ = v___y_4055_;
                    v_prio_x3f_3955_ = v___x_4070_;
                    v___y_3956_ = v___y_4057_;
                    v___y_3957_ = v___y_4058_;
                    state = 29;
                    continue;
                }
            }
            41 => {
                v___x_4085_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_4086_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_4085_);
                v___x_4087_ = l_Lean_Syntax_isNone(v___x_4086_);
                if v___x_4087_ == 0 {
                    crate::leanh::lean_inc(v___x_4086_);
                    v___x_4088_ = l_Lean_Syntax_matchesNull(v___x_4086_, v___y_4080_);
                    if v___x_4088_ == 0 {
                        crate::leanh::lean_dec(v___x_4086_);
                        crate::leanh::lean_dec(v_prec_x3f_4082_);
                        crate::leanh::lean_dec(v___y_4078_);
                        crate::leanh::lean_dec(v___y_4075_);
                        crate::leanh::lean_dec(v___y_4073_);
                        crate::leanh::lean_dec(v___y_4072_);
                        crate::leanh::lean_dec(v_x_3367_);
                        v___x_4089_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                        return v___x_4089_;
                    } else {
                        v___x_4090_ = l_Lean_Syntax_getArg(v___x_4086_, v___x_3542_);
                        crate::leanh::lean_dec(v___x_4086_);
                        v___x_4091_ = l_Lean_Elab_Command_elabMacro___closed__58;
                        crate::leanh::lean_inc(v___x_4090_);
                        v___x_4092_ = l_Lean_Syntax_isOfKind(v___x_4090_, v___x_4091_);
                        if v___x_4092_ == 0 {
                            crate::leanh::lean_dec(v___x_4090_);
                            crate::leanh::lean_dec(v_prec_x3f_4082_);
                            crate::leanh::lean_dec(v___y_4078_);
                            crate::leanh::lean_dec(v___y_4075_);
                            crate::leanh::lean_dec(v___y_4073_);
                            crate::leanh::lean_dec(v___y_4072_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v___x_4093_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                            return v___x_4093_;
                        } else {
                            v_name_x3f_4094_ = l_Lean_Syntax_getArg(v___x_4090_, v___y_4079_);
                            crate::leanh::lean_dec(v___x_4090_);
                            v___x_4095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4095_, 0, v_name_x3f_4094_);
                            v___y_4045_ = v___y_4072_;
                            v___y_4046_ = v___y_4075_;
                            v___y_4047_ = v___y_4074_;
                            v___y_4048_ = v___y_4073_;
                            v___y_4049_ = v___y_4078_;
                            v___y_4050_ = v_prec_x3f_4082_;
                            v___y_4051_ = v___y_4077_;
                            v___y_4052_ = v___y_4076_;
                            v___y_4053_ = v___y_4079_;
                            v___y_4054_ = v___y_4080_;
                            v___y_4055_ = v___y_4081_;
                            v_name_x3f_4056_ = v___x_4095_;
                            v___y_4057_ = v___y_4083_;
                            v___y_4058_ = v___y_4084_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4086_);
                    v___x_4096_ = crate::leanh::lean_box(0);
                    v___y_4045_ = v___y_4072_;
                    v___y_4046_ = v___y_4075_;
                    v___y_4047_ = v___y_4074_;
                    v___y_4048_ = v___y_4073_;
                    v___y_4049_ = v___y_4078_;
                    v___y_4050_ = v_prec_x3f_4082_;
                    v___y_4051_ = v___y_4077_;
                    v___y_4052_ = v___y_4076_;
                    v___y_4053_ = v___y_4079_;
                    v___y_4054_ = v___y_4080_;
                    v___y_4055_ = v___y_4081_;
                    v_name_x3f_4056_ = v___x_4096_;
                    v___y_4057_ = v___y_4083_;
                    v___y_4058_ = v___y_4084_;
                    state = 40;
                    continue;
                }
            }
            42 => {
                v___x_4103_ = crate::leanh::lean_unsigned_to_nat(2);
                v_rulesKind_4104_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_4103_);
                v___x_4105_ = l_Lean_Elab_Command_elabMacro___closed__72;
                v___x_4106_ = l_Lean_Elab_Command_elabMacro___closed__74;
                crate::leanh::lean_inc(v_rulesKind_4104_);
                v___x_4107_ = l_Lean_Syntax_isOfKind(v_rulesKind_4104_, v___x_4106_);
                if v___x_4107_ == 0 {
                    crate::leanh::lean_dec(v_rulesKind_4104_);
                    crate::leanh::lean_dec(v_attrs_x3f_4100_);
                    crate::leanh::lean_dec(v___y_4098_);
                    crate::leanh::lean_dec(v_x_3367_);
                    v___x_4108_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                    return v___x_4108_;
                } else {
                    v___x_4109_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_tk_4110_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_4109_);
                    v___x_4111_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4112_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_4111_);
                    v___x_4113_ = l_Lean_Syntax_isNone(v___x_4112_);
                    if v___x_4113_ == 0 {
                        crate::leanh::lean_inc(v___x_4112_);
                        v___x_4114_ = l_Lean_Syntax_matchesNull(v___x_4112_, v___y_4099_);
                        if v___x_4114_ == 0 {
                            crate::leanh::lean_dec(v___x_4112_);
                            crate::leanh::lean_dec(v_tk_4110_);
                            crate::leanh::lean_dec(v_rulesKind_4104_);
                            crate::leanh::lean_dec(v_attrs_x3f_4100_);
                            crate::leanh::lean_dec(v___y_4098_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v___x_4115_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                            return v___x_4115_;
                        } else {
                            v___x_4116_ = l_Lean_Syntax_getArg(v___x_4112_, v___x_3542_);
                            crate::leanh::lean_dec(v___x_4112_);
                            v___x_4117_ = l_Lean_Elab_Command_elabMacro___closed__61;
                            crate::leanh::lean_inc(v___x_4116_);
                            v___x_4118_ = l_Lean_Syntax_isOfKind(v___x_4116_, v___x_4117_);
                            if v___x_4118_ == 0 {
                                crate::leanh::lean_dec(v___x_4116_);
                                crate::leanh::lean_dec(v_tk_4110_);
                                crate::leanh::lean_dec(v_rulesKind_4104_);
                                crate::leanh::lean_dec(v_attrs_x3f_4100_);
                                crate::leanh::lean_dec(v___y_4098_);
                                crate::leanh::lean_dec(v_x_3367_);
                                v___x_4119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                                return v___x_4119_;
                            } else {
                                v_prec_x3f_4120_ = l_Lean_Syntax_getArg(v___x_4116_, v___y_4099_);
                                crate::leanh::lean_dec(v___x_4116_);
                                v___x_4121_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4121_, 0, v_prec_x3f_4120_);
                                v___y_4072_ = v_rulesKind_4104_;
                                v___y_4073_ = v___y_4098_;
                                v___y_4074_ = v___x_4105_;
                                v___y_4075_ = v_tk_4110_;
                                v___y_4076_ = v___x_4106_;
                                v___y_4077_ = v___x_4107_;
                                v___y_4078_ = v_attrs_x3f_4100_;
                                v___y_4079_ = v___x_4109_;
                                v___y_4080_ = v___y_4099_;
                                v___y_4081_ = v___x_4103_;
                                v_prec_x3f_4082_ = v___x_4121_;
                                v___y_4083_ = v___y_4101_;
                                v___y_4084_ = v___y_4102_;
                                state = 41;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4112_);
                        v___x_4122_ = crate::leanh::lean_box(0);
                        v___y_4072_ = v_rulesKind_4104_;
                        v___y_4073_ = v___y_4098_;
                        v___y_4074_ = v___x_4105_;
                        v___y_4075_ = v_tk_4110_;
                        v___y_4076_ = v___x_4106_;
                        v___y_4077_ = v___x_4107_;
                        v___y_4078_ = v_attrs_x3f_4100_;
                        v___y_4079_ = v___x_4109_;
                        v___y_4080_ = v___y_4099_;
                        v___y_4081_ = v___x_4103_;
                        v_prec_x3f_4082_ = v___x_4122_;
                        v___y_4083_ = v___y_4101_;
                        v___y_4084_ = v___y_4102_;
                        state = 41;
                        continue;
                    }
                }
            }
            43 => {
                v___x_4127_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4128_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_4127_);
                v___x_4129_ = l_Lean_Syntax_isNone(v___x_4128_);
                if v___x_4129_ == 0 {
                    crate::leanh::lean_inc(v___x_4128_);
                    v___x_4130_ = l_Lean_Syntax_matchesNull(v___x_4128_, v___x_4127_);
                    if v___x_4130_ == 0 {
                        crate::leanh::lean_dec(v___x_4128_);
                        crate::leanh::lean_dec(v_doc_x3f_4124_);
                        crate::leanh::lean_dec(v_x_3367_);
                        v___x_4131_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                        return v___x_4131_;
                    } else {
                        v___x_4132_ = l_Lean_Syntax_getArg(v___x_4128_, v___x_3542_);
                        crate::leanh::lean_dec(v___x_4128_);
                        v___x_4133_ = l_Lean_Elab_Command_elabMacro___closed__75;
                        crate::leanh::lean_inc(v___x_4132_);
                        v___x_4134_ = l_Lean_Syntax_isOfKind(v___x_4132_, v___x_4133_);
                        if v___x_4134_ == 0 {
                            crate::leanh::lean_dec(v___x_4132_);
                            crate::leanh::lean_dec(v_doc_x3f_4124_);
                            crate::leanh::lean_dec(v_x_3367_);
                            v___x_4135_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabMacro_spec__0___redArg();
                            return v___x_4135_;
                        } else {
                            v___x_4136_ = l_Lean_Syntax_getArg(v___x_4132_, v___x_4127_);
                            crate::leanh::lean_dec(v___x_4132_);
                            v_attrs_x3f_4137_ = l_Lean_Syntax_getArgs(v___x_4136_);
                            crate::leanh::lean_dec(v___x_4136_);
                            v___x_4138_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4138_, 0, v_attrs_x3f_4137_);
                            v___y_4098_ = v_doc_x3f_4124_;
                            v___y_4099_ = v___x_4127_;
                            v_attrs_x3f_4100_ = v___x_4138_;
                            v___y_4101_ = v___y_4125_;
                            v___y_4102_ = v___y_4126_;
                            state = 42;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4128_);
                    v___x_4139_ = crate::leanh::lean_box(0);
                    v___y_4098_ = v_doc_x3f_4124_;
                    v___y_4099_ = v___x_4127_;
                    v_attrs_x3f_4100_ = v___x_4139_;
                    v___y_4101_ = v___y_4125_;
                    v___y_4102_ = v___y_4126_;
                    state = 42;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabMacro___boxed(
    mut v_x_4151_: *mut crate::leanh::LeanObject,
    mut v_a_4152_: *mut crate::leanh::LeanObject,
    mut v_a_4153_: *mut crate::leanh::LeanObject,
    mut v_a_4154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4155_ = l_Lean_Elab_Command_elabMacro(v_x_4151_, v_a_4152_, v_a_4153_);
    crate::leanh::lean_dec(v_a_4153_);
    crate::leanh::lean_dec_ref(v_a_4152_);
    return v_res_4155_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2(
    mut v_00_u03b1_4156_: *mut crate::leanh::LeanObject,
    mut v_x_4157_: *mut crate::leanh::LeanObject,
    mut v___y_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___redArg(v_x_4157_, v___y_4159_);
    return v___x_4160_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2___boxed(
    mut v_00_u03b1_4161_: *mut crate::leanh::LeanObject,
    mut v_x_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
    mut v___y_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4165_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__2(v_00_u03b1_4161_, v_x_4162_, v___y_4163_, v___y_4164_);
    crate::leanh::lean_dec_ref(v___y_4163_);
    crate::leanh::lean_dec_ref(v_x_4162_);
    return v_res_4165_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7(
    mut v_00_u03b1_4166_: *mut crate::leanh::LeanObject,
    mut v_ref_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4171_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___redArg(v_ref_4167_);
    return v___x_4171_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7___boxed(
    mut v_00_u03b1_4172_: *mut crate::leanh::LeanObject,
    mut v_ref_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4177_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__7(v_00_u03b1_4172_, v_ref_4173_, v___y_4174_, v___y_4175_);
    crate::leanh::lean_dec(v___y_4175_);
    crate::leanh::lean_dec_ref(v___y_4174_);
    return v_res_4177_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1(
    mut v_00_u03b1_4178_: *mut crate::leanh::LeanObject,
    mut v_x_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4183_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___redArg(
        v_x_4179_,
        v___y_4180_,
        v___y_4181_,
    );
    return v___x_4183_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1___boxed(
    mut v_00_u03b1_4184_: *mut crate::leanh::LeanObject,
    mut v_x_4185_: *mut crate::leanh::LeanObject,
    mut v___y_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4189_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1(
        v_00_u03b1_4184_,
        v_x_4185_,
        v___y_4186_,
        v___y_4187_,
    );
    crate::leanh::lean_dec(v___y_4187_);
    crate::leanh::lean_dec_ref(v___y_4186_);
    return v_res_4189_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3(
    mut v_msgData_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4194_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___redArg(v_msgData_4190_, v___y_4192_);
    return v___x_4194_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_4195_: *mut crate::leanh::LeanObject,
    mut v___y_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4199_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__1_spec__3(v_msgData_4195_, v___y_4196_, v___y_4197_);
    crate::leanh::lean_dec(v___y_4197_);
    crate::leanh::lean_dec_ref(v___y_4196_);
    return v_res_4199_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4(
    mut v_as_4200_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4201_: *mut crate::leanh::LeanObject,
    mut v_b_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v___y_4204_: *mut crate::leanh::LeanObject,
    mut v___y_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4207_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4___redArg(v_as_x27_4201_, v_b_4202_, v___y_4204_, v___y_4205_);
    return v___x_4207_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4___boxed(
    mut v_as_4208_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4209_: *mut crate::leanh::LeanObject,
    mut v_b_4210_: *mut crate::leanh::LeanObject,
    mut v_a_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__4(v_as_4208_, v_as_x27_4209_, v_b_4210_, v_a_4211_, v___y_4212_, v___y_4213_);
    crate::leanh::lean_dec(v___y_4213_);
    crate::leanh::lean_dec_ref(v___y_4212_);
    crate::leanh::lean_dec(v_as_x27_4209_);
    crate::leanh::lean_dec(v_as_4208_);
    return v_res_4215_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6(
    mut v_00_u03b1_4216_: *mut crate::leanh::LeanObject,
    mut v_ref_4217_: *mut crate::leanh::LeanObject,
    mut v_msg_4218_: *mut crate::leanh::LeanObject,
    mut v___y_4219_: *mut crate::leanh::LeanObject,
    mut v___y_4220_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4222_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6___redArg(v_ref_4217_, v_msg_4218_, v___y_4219_, v___y_4220_);
    return v___x_4222_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6___boxed(
    mut v_00_u03b1_4223_: *mut crate::leanh::LeanObject,
    mut v_ref_4224_: *mut crate::leanh::LeanObject,
    mut v_msg_4225_: *mut crate::leanh::LeanObject,
    mut v___y_4226_: *mut crate::leanh::LeanObject,
    mut v___y_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4229_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6(v_00_u03b1_4223_, v_ref_4224_, v_msg_4225_, v___y_4226_, v___y_4227_);
    crate::leanh::lean_dec(v___y_4227_);
    crate::leanh::lean_dec_ref(v___y_4226_);
    crate::leanh::lean_dec(v_ref_4224_);
    return v_res_4229_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8(
    mut v_00_u03b2_4230_: *mut crate::leanh::LeanObject,
    mut v_m_4231_: *mut crate::leanh::LeanObject,
    mut v_a_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4233_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___redArg(v_m_4231_, v_a_4232_);
    return v___x_4233_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_4234_: *mut crate::leanh::LeanObject,
    mut v_m_4235_: *mut crate::leanh::LeanObject,
    mut v_a_4236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4237_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8(v_00_u03b2_4234_, v_m_4235_, v_a_4236_);
    crate::leanh::lean_dec(v_a_4236_);
    crate::leanh::lean_dec_ref(v_m_4235_);
    return v_res_4237_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12(
    mut v_00_u03b1_4238_: *mut crate::leanh::LeanObject,
    mut v_msg_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
    mut v___y_4241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4243_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12___redArg(v_msg_4239_, v___y_4240_, v___y_4241_);
    return v___x_4243_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12___boxed(
    mut v_00_u03b1_4244_: *mut crate::leanh::LeanObject,
    mut v_msg_4245_: *mut crate::leanh::LeanObject,
    mut v___y_4246_: *mut crate::leanh::LeanObject,
    mut v___y_4247_: *mut crate::leanh::LeanObject,
    mut v___y_4248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4249_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12(v_00_u03b1_4244_, v_msg_4245_, v___y_4246_, v___y_4247_);
    crate::leanh::lean_dec(v___y_4247_);
    crate::leanh::lean_dec_ref(v___y_4246_);
    return v_res_4249_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10(
    mut v_00_u03b2_4250_: *mut crate::leanh::LeanObject,
    mut v_x_4251_: *mut crate::leanh::LeanObject,
    mut v_x_4252_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4253_: u8 = 0;
    v___x_4253_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10___redArg(v_x_4251_, v_x_4252_);
    return v___x_4253_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10___boxed(
    mut v_00_u03b2_4254_: *mut crate::leanh::LeanObject,
    mut v_x_4255_: *mut crate::leanh::LeanObject,
    mut v_x_4256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4257_: u8 = 0;
    let mut v_r_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4257_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10(v_00_u03b2_4254_, v_x_4255_, v_x_4256_);
    crate::leanh::lean_dec_ref(v_x_4256_);
    crate::leanh::lean_dec_ref(v_x_4255_);
    v_r_4258_ = crate::leanh::lean_box((v_res_4257_) as usize);
    return v_r_4258_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13(
    mut v_00_u03b2_4259_: *mut crate::leanh::LeanObject,
    mut v_a_4260_: *mut crate::leanh::LeanObject,
    mut v_x_4261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13___redArg(v_a_4260_, v_x_4261_);
    return v___x_4262_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13___boxed(
    mut v_00_u03b2_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_x_4265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4266_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__8_spec__13(v_00_u03b2_4263_, v_a_4264_, v_x_4265_);
    crate::leanh::lean_dec(v_x_4265_);
    crate::leanh::lean_dec(v_a_4264_);
    return v_res_4266_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18(
    mut v_msgData_4267_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4268_: *mut crate::leanh::LeanObject,
    mut v___y_4269_: *mut crate::leanh::LeanObject,
    mut v___y_4270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4272_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___redArg(v_msgData_4267_, v_macroStack_4268_, v___y_4270_);
    return v___x_4272_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18___boxed(
    mut v_msgData_4273_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
    mut v___y_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4278_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__6_spec__12_spec__18(v_msgData_4273_, v_macroStack_4274_, v___y_4275_, v___y_4276_);
    crate::leanh::lean_dec(v___y_4276_);
    crate::leanh::lean_dec_ref(v___y_4275_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14(
    mut v_00_u03b2_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
    mut v_x_4281_: usize,
    mut v_x_4282_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4283_: u8 = 0;
    v___x_4283_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___redArg(v_x_4280_, v_x_4281_, v_x_4282_);
    return v___x_4283_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14___boxed(
    mut v_00_u03b2_4284_: *mut crate::leanh::LeanObject,
    mut v_x_4285_: *mut crate::leanh::LeanObject,
    mut v_x_4286_: *mut crate::leanh::LeanObject,
    mut v_x_4287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_33608__boxed_4288_: usize = 0;
    let mut v_res_4289_: u8 = 0;
    let mut v_r_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_33608__boxed_4288_ = crate::leanh::lean_unbox_usize(v_x_4286_);
    crate::leanh::lean_dec(v_x_4286_);
    v_res_4289_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14(v_00_u03b2_4284_, v_x_4285_, v_x_33608__boxed_4288_, v_x_4287_);
    crate::leanh::lean_dec_ref(v_x_4287_);
    crate::leanh::lean_dec_ref(v_x_4285_);
    v_r_4290_ = crate::leanh::lean_box((v_res_4289_) as usize);
    return v_r_4290_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18(
    mut v_00_u03b2_4291_: *mut crate::leanh::LeanObject,
    mut v_keys_4292_: *mut crate::leanh::LeanObject,
    mut v_vals_4293_: *mut crate::leanh::LeanObject,
    mut v_heq_4294_: *mut crate::leanh::LeanObject,
    mut v_i_4295_: *mut crate::leanh::LeanObject,
    mut v_k_4296_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4297_: u8 = 0;
    v___x_4297_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___redArg(v_keys_4292_, v_i_4295_, v_k_4296_);
    return v___x_4297_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18___boxed(
    mut v_00_u03b2_4298_: *mut crate::leanh::LeanObject,
    mut v_keys_4299_: *mut crate::leanh::LeanObject,
    mut v_vals_4300_: *mut crate::leanh::LeanObject,
    mut v_heq_4301_: *mut crate::leanh::LeanObject,
    mut v_i_4302_: *mut crate::leanh::LeanObject,
    mut v_k_4303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4304_: u8 = 0;
    let mut v_r_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4304_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabMacro_spec__1_spec__3_spec__6_spec__10_spec__14_spec__18(v_00_u03b2_4298_, v_keys_4299_, v_vals_4300_, v_heq_4301_, v_i_4302_, v_k_4303_);
    crate::leanh::lean_dec_ref(v_k_4303_);
    crate::leanh::lean_dec_ref(v_vals_4300_);
    crate::leanh::lean_dec_ref(v_keys_4299_);
    v_r_4305_ = crate::leanh::lean_box((v_res_4304_) as usize);
    return v_r_4305_;
}
pub unsafe fn l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4313_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_4314_ = l_Lean_Elab_Command_elabMacro___closed__45;
    v___x_4315_ = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1;
    v___x_4316_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabMacro___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_4317_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_4313_,
        v___x_4314_,
        v___x_4315_,
        v___x_4316_,
    );
    return v___x_4317_;
}
pub unsafe fn l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___boxed(
    mut v_a_4318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4319_ = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1();
    return v_res_4319_;
}
pub unsafe fn l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1___closed__1;
    v___x_4347_ = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___closed__6;
    v___x_4348_ = l_Lean_addBuiltinDeclarationRanges(v___x_4346_, v___x_4347_);
    return v___x_4348_;
}
pub unsafe fn l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3___boxed(
    mut v_a_4349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4350_ = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3();
    return v_res_4350_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Macro(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_MacroArgUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Macro_0__Lean_Elab_Command_elabMacro___regBuiltin_Lean_Elab_Command_elabMacro_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Macro(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Macro(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_MacroArgUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Macro(builtin);
}
