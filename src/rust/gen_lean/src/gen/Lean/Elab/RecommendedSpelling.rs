// Lean compiler output
// Module: Lean.Elab.RecommendedSpelling
// Imports: Lean.Elab.Command
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land,
    lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_isNone, l_Lean_TSyntax_getDocString, l_Lean_TSyntax_getString,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_beq___boxed, l_Lean_Name_hash___override___boxed,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_liftTermElabM___redArg,
    runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo;
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg, l_Lean_instInhabitedEffectiveImport_default,
    l_Lean_instInhabitedPersistentEnvExtensionState___redArg,
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
use crate::r#gen::Lean::Parser::Term::Doc::{
    l_Lean_Parser_Term_Doc_addRecommendedSpelling, l_Lean_Parser_Term_Doc_recommendedSpellingExt,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__1: usize = 0;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__10_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__13_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__20_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__0_value:
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
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__1_value:
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
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__2_value:
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
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__3_value:
    crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        114, 101, 99, 111, 109, 109, 101, 110, 100, 101, 100, 95, 115, 112, 101, 108, 108, 105,
        110, 103, 0,
    ],
};
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__3_value)
            as *mut crate::leanh::LeanObject,
        5104810461247945287 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__5_value:
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
        77, 97, 108, 102, 111, 114, 109, 101, 100, 32, 114, 101, 99, 111, 109, 109, 101, 110, 100,
        101, 100, 32, 115, 112, 101, 108, 108, 105, 110, 103, 32, 99, 111, 109, 109, 97, 110, 100,
        0,
    ],
};
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__7_value:
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
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__8_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__7_value)
            as *mut crate::leanh::LeanObject,
        9232979286016572671 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__9_value:
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
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__10_value:
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
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__2_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__10_value)
            as *mut crate::leanh::LeanObject,
        9063780239635860524 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed__const__1_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut crate::leanh::LeanObject)],
};
pub static mut l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed__const__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [68, 111, 99, 0]};
static mut l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__3_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [101, 108, 97, 98, 82, 101, 99, 111, 109, 109, 101, 110, 100, 101, 100, 83, 112, 101, 108, 108, 105, 110, 103, 0]};
static mut l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__1_value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__2_value) as *mut crate::leanh::LeanObject,6077625762660070556 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__3_value) as *mut crate::leanh::LeanObject,16996917054240796530 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__2_value:
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
static mut l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1(
    mut v_sz_1059_: usize,
    mut v_i_1060_: usize,
    mut v_bs_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: usize = 0;
    let mut v___x_1071_: usize = 0;
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1062_ = lean_usize_dec_lt(v_i_1060_, v_sz_1059_);
                if v___x_1062_ == 0 {
                    v___x_1063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1063_, 0, v_bs_1061_);
                    return v___x_1063_;
                } else {
                    v_v_1064_ = lean_array_uget(v_bs_1061_, v_i_1060_);
                    v___x_1065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___closed__1;
                    crate::leanh::lean_inc(v_v_1064_);
                    v___x_1066_ = l_Lean_Syntax_isOfKind(v_v_1064_, v___x_1065_);
                    if v___x_1066_ == 0 {
                        crate::leanh::lean_dec(v_v_1064_);
                        crate::leanh::lean_dec_ref(v_bs_1061_);
                        v___x_1067_ = crate::leanh::lean_box(0);
                        return v___x_1067_;
                    } else {
                        v___x_1068_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1069_ = lean_array_uset(v_bs_1061_, v_i_1060_, v___x_1068_);
                        v___x_1070_ = 1usize;
                        v___x_1071_ = lean_usize_add(v_i_1060_, v___x_1070_);
                        v___x_1072_ = lean_array_uset(v_bs_x27_1069_, v_i_1060_, v_v_1064_);
                        v_i_1060_ = v___x_1071_;
                        v_bs_1061_ = v___x_1072_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___boxed(
    mut v_sz_1074_: *mut crate::leanh::LeanObject,
    mut v_i_1075_: *mut crate::leanh::LeanObject,
    mut v_bs_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1077_: usize = 0;
    let mut v_i_boxed_1078_: usize = 0;
    let mut v_res_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1077_ = crate::leanh::lean_unbox_usize(v_sz_1074_);
    crate::leanh::lean_dec(v_sz_1074_);
    v_i_boxed_1078_ = crate::leanh::lean_unbox_usize(v_i_1075_);
    crate::leanh::lean_dec(v_i_1075_);
    v_res_1079_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1(v_sz_boxed_1077_, v_i_boxed_1078_, v_bs_1076_);
    return v_res_1079_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3___redArg(
    mut v_sz_1080_: usize,
    mut v_i_1081_: usize,
    mut v_bs_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1086_: u8 = 0;
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: usize = 0;
    let mut v___x_1095_: usize = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1101_: u8 = 0;
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1105_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1086_ = lean_usize_dec_lt(v_i_1081_, v_sz_1080_);
                if v___x_1086_ == 0 {
                    v___x_1087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1087_, 0, v_bs_1082_);
                    return v___x_1087_;
                } else {
                    v_v_1088_ = lean_array_uget_borrowed(v_bs_1082_, v_i_1081_);
                    v___x_1089_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc(v_v_1088_);
                    v___x_1090_ = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(
                        v_v_1088_,
                        v___x_1089_,
                        v___y_1083_,
                        v___y_1084_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1090_) == 0 {
                        v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                        crate::leanh::lean_inc(v_a_1091_);
                        crate::leanh::lean_dec_ref_known(v___x_1090_, 1);
                        v___x_1092_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_1093_ = lean_array_uset(v_bs_1082_, v_i_1081_, v___x_1092_);
                        v___x_1094_ = 1usize;
                        v___x_1095_ = lean_usize_add(v_i_1081_, v___x_1094_);
                        v___x_1096_ = lean_array_uset(v_bs_x27_1093_, v_i_1081_, v_a_1091_);
                        v_i_1081_ = v___x_1095_;
                        v_bs_1082_ = v___x_1096_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_1082_);
                        v_a_1098_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                        v_isSharedCheck_1105_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                        if v_isSharedCheck_1105_ == 0 {
                            v___x_1100_ = v___x_1090_;
                            v_isShared_1101_ = v_isSharedCheck_1105_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1098_);
                            crate::leanh::lean_dec(v___x_1090_);
                            v___x_1100_ = crate::leanh::lean_box(0);
                            v_isShared_1101_ = v_isSharedCheck_1105_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1101_ == 0 {
                    v___x_1103_ = v___x_1100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1104_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
                    v___x_1103_ = v_reuseFailAlloc_1104_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1103_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3___redArg___boxed(
    mut v_sz_1106_: *mut crate::leanh::LeanObject,
    mut v_i_1107_: *mut crate::leanh::LeanObject,
    mut v_bs_1108_: *mut crate::leanh::LeanObject,
    mut v___y_1109_: *mut crate::leanh::LeanObject,
    mut v___y_1110_: *mut crate::leanh::LeanObject,
    mut v___y_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1112_: usize = 0;
    let mut v_i_boxed_1113_: usize = 0;
    let mut v_res_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1112_ = crate::leanh::lean_unbox_usize(v_sz_1106_);
    crate::leanh::lean_dec(v_sz_1106_);
    v_i_boxed_1113_ = crate::leanh::lean_unbox_usize(v_i_1107_);
    crate::leanh::lean_dec(v_i_1107_);
    v_res_1114_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3___redArg(v_sz_boxed_1112_, v_i_boxed_1113_, v_bs_1108_, v___y_1109_, v___y_1110_);
    crate::leanh::lean_dec(v___y_1110_);
    crate::leanh::lean_dec_ref(v___y_1109_);
    return v_res_1114_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3(
    mut v_sz_1115_: usize,
    mut v_i_1116_: usize,
    mut v_bs_1117_: *mut crate::leanh::LeanObject,
    mut v___y_1118_: *mut crate::leanh::LeanObject,
    mut v___y_1119_: *mut crate::leanh::LeanObject,
    mut v___y_1120_: *mut crate::leanh::LeanObject,
    mut v___y_1121_: *mut crate::leanh::LeanObject,
    mut v___y_1122_: *mut crate::leanh::LeanObject,
    mut v___y_1123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3___redArg(v_sz_1115_, v_i_1116_, v_bs_1117_, v___y_1122_, v___y_1123_);
    return v___x_1125_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3___boxed(
    mut v_sz_1126_: *mut crate::leanh::LeanObject,
    mut v_i_1127_: *mut crate::leanh::LeanObject,
    mut v_bs_1128_: *mut crate::leanh::LeanObject,
    mut v___y_1129_: *mut crate::leanh::LeanObject,
    mut v___y_1130_: *mut crate::leanh::LeanObject,
    mut v___y_1131_: *mut crate::leanh::LeanObject,
    mut v___y_1132_: *mut crate::leanh::LeanObject,
    mut v___y_1133_: *mut crate::leanh::LeanObject,
    mut v___y_1134_: *mut crate::leanh::LeanObject,
    mut v___y_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1136_: usize = 0;
    let mut v_i_boxed_1137_: usize = 0;
    let mut v_res_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1136_ = crate::leanh::lean_unbox_usize(v_sz_1126_);
    crate::leanh::lean_dec(v_sz_1126_);
    v_i_boxed_1137_ = crate::leanh::lean_unbox_usize(v_i_1127_);
    crate::leanh::lean_dec(v_i_1127_);
    v_res_1138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3(v_sz_boxed_1136_, v_i_boxed_1137_, v_bs_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_);
    crate::leanh::lean_dec(v___y_1134_);
    crate::leanh::lean_dec_ref(v___y_1133_);
    crate::leanh::lean_dec(v___y_1132_);
    crate::leanh::lean_dec_ref(v___y_1131_);
    crate::leanh::lean_dec(v___y_1130_);
    crate::leanh::lean_dec_ref(v___y_1129_);
    return v_res_1138_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__5(
    mut v___x_1139_: u8,
    mut v_as_1140_: *mut crate::leanh::LeanObject,
    mut v_i_1141_: usize,
    mut v_stop_1142_: usize,
    mut v_b_1143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: usize = 0;
    let mut v___x_1147_: usize = 0;
    let mut v___x_1149_: u8 = 0;
    let mut v_fst_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v_snd_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1155_: u8 = 0;
    let mut v___x_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_unused_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1172_: u8 = 0;
    let mut v_unused_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1149_ = lean_usize_dec_eq(v_i_1141_, v_stop_1142_);
                if v___x_1149_ == 0 {
                    v_fst_1150_ = crate::leanh::lean_ctor_get(v_b_1143_, 0);
                    v___x_1151_ = (crate::leanh::lean_unbox(v_fst_1150_) as u8);
                    if v___x_1151_ == 0 {
                        v_snd_1152_ = crate::leanh::lean_ctor_get(v_b_1143_, 1);
                        v_isSharedCheck_1160_ = (!crate::leanh::lean_is_exclusive(v_b_1143_)) as u8;
                        if v_isSharedCheck_1160_ == 0 {
                            v_unused_1161_ = crate::leanh::lean_ctor_get(v_b_1143_, 0);
                            crate::leanh::lean_dec(v_unused_1161_);
                            v___x_1154_ = v_b_1143_;
                            v_isShared_1155_ = v_isSharedCheck_1160_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1152_);
                            crate::leanh::lean_dec(v_b_1143_);
                            v___x_1154_ = crate::leanh::lean_box(0);
                            v_isShared_1155_ = v_isSharedCheck_1160_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_snd_1162_ = crate::leanh::lean_ctor_get(v_b_1143_, 1);
                        v_isSharedCheck_1172_ = (!crate::leanh::lean_is_exclusive(v_b_1143_)) as u8;
                        if v_isSharedCheck_1172_ == 0 {
                            v_unused_1173_ = crate::leanh::lean_ctor_get(v_b_1143_, 0);
                            crate::leanh::lean_dec(v_unused_1173_);
                            v___x_1164_ = v_b_1143_;
                            v_isShared_1165_ = v_isSharedCheck_1172_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_1162_);
                            crate::leanh::lean_dec(v_b_1143_);
                            v___x_1164_ = crate::leanh::lean_box(0);
                            v_isShared_1165_ = v_isSharedCheck_1172_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    return v_b_1143_;
                }
            }
            1 => {
                v___x_1146_ = 1usize;
                v___x_1147_ = lean_usize_add(v_i_1141_, v___x_1146_);
                v_i_1141_ = v___x_1147_;
                v_b_1143_ = v___y_1145_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1156_ = crate::leanh::lean_box((v___x_1139_) as usize);
                if v_isShared_1155_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1154_, 0, v___x_1156_);
                    v___x_1158_ = v___x_1154_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 1, v_snd_1152_);
                    v___x_1158_ = v_reuseFailAlloc_1159_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_1145_ = v___x_1158_;
                state = 1;
                continue;
            }
            4 => {
                v___x_1166_ = lean_array_uget_borrowed(v_as_1140_, v_i_1141_);
                crate::leanh::lean_inc(v___x_1166_);
                v___x_1167_ = lean_array_push(v_snd_1162_, v___x_1166_);
                v___x_1168_ = crate::leanh::lean_box((v___x_1149_) as usize);
                if v_isShared_1165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1164_, 1, v___x_1167_);
                    crate::leanh::lean_ctor_set(v___x_1164_, 0, v___x_1168_);
                    v___x_1170_ = v___x_1164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 0, v___x_1168_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1171_, 1, v___x_1167_);
                    v___x_1170_ = v_reuseFailAlloc_1171_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_1145_ = v___x_1170_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__5___boxed(
    mut v___x_1174_: *mut crate::leanh::LeanObject,
    mut v_as_1175_: *mut crate::leanh::LeanObject,
    mut v_i_1176_: *mut crate::leanh::LeanObject,
    mut v_stop_1177_: *mut crate::leanh::LeanObject,
    mut v_b_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8382__boxed_1179_: u8 = 0;
    let mut v_i_boxed_1180_: usize = 0;
    let mut v_stop_boxed_1181_: usize = 0;
    let mut v_res_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8382__boxed_1179_ = (crate::leanh::lean_unbox(v___x_1174_) as u8);
    v_i_boxed_1180_ = crate::leanh::lean_unbox_usize(v_i_1176_);
    crate::leanh::lean_dec(v_i_1176_);
    v_stop_boxed_1181_ = crate::leanh::lean_unbox_usize(v_stop_1177_);
    crate::leanh::lean_dec(v_stop_1177_);
    v_res_1182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__5(v___x_8382__boxed_1179_, v_as_1175_, v_i_boxed_1180_, v_stop_boxed_1181_, v_b_1178_);
    crate::leanh::lean_dec_ref(v_as_1175_);
    return v_res_1182_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11___redArg(
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_x_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: u8 = 0;
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1184_) == 0 {
                    v___x_1185_ = crate::leanh::lean_box(0);
                    return v___x_1185_;
                } else {
                    v_key_1186_ = crate::leanh::lean_ctor_get(v_x_1184_, 0);
                    v_value_1187_ = crate::leanh::lean_ctor_get(v_x_1184_, 1);
                    v_tail_1188_ = crate::leanh::lean_ctor_get(v_x_1184_, 2);
                    v___x_1189_ = lean_name_eq(v_key_1186_, v_a_1183_);
                    if v___x_1189_ == 0 {
                        v_x_1184_ = v_tail_1188_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_1187_);
                        v___x_1191_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1191_, 0, v_value_1187_);
                        return v___x_1191_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11___redArg___boxed(
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_x_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11___redArg(v_a_1192_, v_x_1193_);
    crate::leanh::lean_dec(v_x_1193_);
    crate::leanh::lean_dec(v_a_1192_);
    return v_res_1194_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1196_: u64 = 0;
    v___x_1195_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_1196_ = lean_uint64_of_nat(v___x_1195_);
    return v___x_1196_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg(
    mut v_m_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1202_: u64 = 0;
    let mut v___x_1203_: u64 = 0;
    let mut v___x_1204_: u64 = 0;
    let mut v_fold_1205_: u64 = 0;
    let mut v___x_1206_: u64 = 0;
    let mut v___x_1207_: u64 = 0;
    let mut v___x_1208_: u64 = 0;
    let mut v___x_1209_: usize = 0;
    let mut v___x_1210_: usize = 0;
    let mut v___x_1211_: usize = 0;
    let mut v___x_1212_: usize = 0;
    let mut v___x_1213_: usize = 0;
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: u64 = 0;
    let mut v_hash_1217_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_1199_ = crate::leanh::lean_ctor_get(v_m_1197_, 1);
                v___x_1200_ = lean_array_get_size(v_buckets_1199_);
                if crate::leanh::lean_obj_tag(v_a_1198_) == 0 {
                    v___x_1216_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___closed__0);
                    v___y_1202_ = v___x_1216_;
                    state = 1;
                    continue;
                } else {
                    v_hash_1217_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_1198_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_1202_ = v_hash_1217_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1203_ = 32u64;
                v___x_1204_ = lean_uint64_shift_right(v___y_1202_, v___x_1203_);
                v_fold_1205_ = lean_uint64_xor(v___y_1202_, v___x_1204_);
                v___x_1206_ = 16u64;
                v___x_1207_ = lean_uint64_shift_right(v_fold_1205_, v___x_1206_);
                v___x_1208_ = lean_uint64_xor(v_fold_1205_, v___x_1207_);
                v___x_1209_ = lean_uint64_to_usize(v___x_1208_);
                v___x_1210_ = lean_usize_of_nat(v___x_1200_);
                v___x_1211_ = 1usize;
                v___x_1212_ = lean_usize_sub(v___x_1210_, v___x_1211_);
                v___x_1213_ = lean_usize_land(v___x_1209_, v___x_1212_);
                v___x_1214_ = lean_array_uget_borrowed(v_buckets_1199_, v___x_1213_);
                v___x_1215_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11___redArg(v_a_1198_, v___x_1214_);
                return v___x_1215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg___boxed(
    mut v_m_1218_: *mut crate::leanh::LeanObject,
    mut v_a_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1220_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg(v_m_1218_, v_a_1219_);
    crate::leanh::lean_dec(v_a_1219_);
    crate::leanh::lean_dec_ref(v_m_1218_);
    return v_res_1220_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14___redArg(
    mut v_keys_1221_: *mut crate::leanh::LeanObject,
    mut v_i_1222_: *mut crate::leanh::LeanObject,
    mut v_k_1223_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: u8 = 0;
    let mut v_k_x27_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1224_ = lean_array_get_size(v_keys_1221_);
                v___x_1225_ = lean_nat_dec_lt(v_i_1222_, v___x_1224_);
                if v___x_1225_ == 0 {
                    crate::leanh::lean_dec(v_i_1222_);
                    return v___x_1225_;
                } else {
                    v_k_x27_1226_ = lean_array_fget_borrowed(v_keys_1221_, v_i_1222_);
                    v___x_1227_ = l_Lean_instBEqExtraModUse_beq(v_k_1223_, v_k_x27_1226_);
                    if v___x_1227_ == 0 {
                        v___x_1228_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1229_ = lean_nat_add(v_i_1222_, v___x_1228_);
                        crate::leanh::lean_dec(v_i_1222_);
                        v_i_1222_ = v___x_1229_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_1222_);
                        return v___x_1227_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14___redArg___boxed(
    mut v_keys_1231_: *mut crate::leanh::LeanObject,
    mut v_i_1232_: *mut crate::leanh::LeanObject,
    mut v_k_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1234_: u8 = 0;
    let mut v_r_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1234_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_1231_, v_i_1232_, v_k_1233_);
    crate::leanh::lean_dec_ref(v_k_1233_);
    crate::leanh::lean_dec_ref(v_keys_1231_);
    v_r_1235_ = crate::leanh::lean_box((v_res_1234_) as usize);
    return v_r_1235_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__0()
-> usize {
    let mut v___x_1236_: usize = 0;
    let mut v___x_1237_: usize = 0;
    let mut v___x_1238_: usize = 0;
    v___x_1236_ = 5usize;
    v___x_1237_ = 1usize;
    v___x_1238_ = lean_usize_shift_left(v___x_1237_, v___x_1236_);
    return v___x_1238_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__1()
-> usize {
    let mut v___x_1239_: usize = 0;
    let mut v___x_1240_: usize = 0;
    let mut v___x_1241_: usize = 0;
    v___x_1239_ = 1usize;
    v___x_1240_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__0);
    v___x_1241_ = lean_usize_sub(v___x_1240_, v___x_1239_);
    return v___x_1241_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg(
    mut v_x_1242_: *mut crate::leanh::LeanObject,
    mut v_x_1243_: usize,
    mut v_x_1244_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: usize = 0;
    let mut v___x_1248_: usize = 0;
    let mut v___x_1249_: usize = 0;
    let mut v_j_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: u8 = 0;
    let mut v_node_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: usize = 0;
    let mut v___x_1257_: u8 = 0;
    let mut v_ks_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1242_) == 0 {
                    v_es_1245_ = crate::leanh::lean_ctor_get(v_x_1242_, 0);
                    v___x_1246_ = crate::leanh::lean_box(2);
                    v___x_1247_ = 5usize;
                    v___x_1248_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___closed__1);
                    v___x_1249_ = lean_usize_land(v_x_1243_, v___x_1248_);
                    v_j_1250_ = lean_usize_to_nat(v___x_1249_);
                    v___x_1251_ = lean_array_get_borrowed(v___x_1246_, v_es_1245_, v_j_1250_);
                    crate::leanh::lean_dec(v_j_1250_);
                    match crate::leanh::lean_obj_tag(v___x_1251_) {
                        0 => {
                            v_key_1252_ = crate::leanh::lean_ctor_get(v___x_1251_, 0);
                            v___x_1253_ = l_Lean_instBEqExtraModUse_beq(v_x_1244_, v_key_1252_);
                            return v___x_1253_;
                        }
                        1 => {
                            v_node_1254_ = crate::leanh::lean_ctor_get(v___x_1251_, 0);
                            v___x_1255_ = lean_usize_shift_right(v_x_1243_, v___x_1247_);
                            v_x_1242_ = v_node_1254_;
                            v_x_1243_ = v___x_1255_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1257_ = 0;
                            return v___x_1257_;
                        }
                    }
                } else {
                    v_ks_1258_ = crate::leanh::lean_ctor_get(v_x_1242_, 0);
                    v___x_1259_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1260_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_ks_1258_, v___x_1259_, v_x_1244_);
                    return v___x_1260_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg___boxed(
    mut v_x_1261_: *mut crate::leanh::LeanObject,
    mut v_x_1262_: *mut crate::leanh::LeanObject,
    mut v_x_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8528__boxed_1264_: usize = 0;
    let mut v_res_1265_: u8 = 0;
    let mut v_r_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8528__boxed_1264_ = crate::leanh::lean_unbox_usize(v_x_1262_);
    crate::leanh::lean_dec(v_x_1262_);
    v_res_1265_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg(v_x_1261_, v_x_8528__boxed_1264_, v_x_1263_);
    crate::leanh::lean_dec_ref(v_x_1263_);
    crate::leanh::lean_dec_ref(v_x_1261_);
    v_r_1266_ = crate::leanh::lean_box((v_res_1265_) as usize);
    return v_r_1266_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7___redArg(
    mut v_x_1267_: *mut crate::leanh::LeanObject,
    mut v_x_1268_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1269_: u64 = 0;
    let mut v___x_1270_: usize = 0;
    let mut v___x_1271_: u8 = 0;
    v___x_1269_ = l_Lean_instHashableExtraModUse_hash(v_x_1268_);
    v___x_1270_ = lean_uint64_to_usize(v___x_1269_);
    v___x_1271_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg(v_x_1267_, v___x_1270_, v_x_1268_);
    return v___x_1271_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7___redArg___boxed(
    mut v_x_1272_: *mut crate::leanh::LeanObject,
    mut v_x_1273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1274_: u8 = 0;
    let mut v_r_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1274_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7___redArg(v_x_1272_, v_x_1273_);
    crate::leanh::lean_dec_ref(v_x_1273_);
    crate::leanh::lean_dec_ref(v_x_1272_);
    v_r_1275_ = crate::leanh::lean_box((v_res_1274_) as usize);
    return v_r_1275_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1276_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1276_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1277_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__0);
    v___x_1278_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1278_, 0, v___x_1277_);
    return v___x_1278_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1279_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1);
    v___x_1280_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1281_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1281_, 0, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 1, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 2, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 3, v___x_1280_);
    crate::leanh::lean_ctor_set(v___x_1281_, 4, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 5, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 6, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 7, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 8, v___x_1279_);
    crate::leanh::lean_ctor_set(v___x_1281_, 9, v___x_1279_);
    return v___x_1281_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1282_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1283_ = lean_mk_empty_array_with_capacity(v___x_1282_);
    v___x_1284_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1284_, 0, v___x_1283_);
    return v___x_1284_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1285_: usize = 0;
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1285_ = 5usize;
    v___x_1286_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1287_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
    v___x_1289_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__3);
    v___x_1290_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1290_, 0, v___x_1289_);
    crate::leanh::lean_ctor_set(v___x_1290_, 1, v___x_1288_);
    crate::leanh::lean_ctor_set(v___x_1290_, 2, v___x_1286_);
    crate::leanh::lean_ctor_set(v___x_1290_, 3, v___x_1286_);
    crate::leanh::lean_ctor_set_usize(v___x_1290_, 4, v___x_1285_);
    return v___x_1290_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1291_ = crate::leanh::lean_box(1);
    v___x_1292_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__4);
    v___x_1293_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__1);
    v___x_1294_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1294_, 0, v___x_1293_);
    crate::leanh::lean_ctor_set(v___x_1294_, 1, v___x_1292_);
    crate::leanh::lean_ctor_set(v___x_1294_, 2, v___x_1291_);
    return v___x_1294_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg(
    mut v_msgData_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1298_ = lean_st_ref_get(v___y_1296_);
    v_env_1299_ = crate::leanh::lean_ctor_get(v___x_1298_, 0);
    crate::leanh::lean_inc_ref(v_env_1299_);
    crate::leanh::lean_dec(v___x_1298_);
    v___x_1300_ = lean_st_ref_get(v___y_1296_);
    v_scopes_1301_ = crate::leanh::lean_ctor_get(v___x_1300_, 2);
    crate::leanh::lean_inc(v_scopes_1301_);
    crate::leanh::lean_dec(v___x_1300_);
    v___x_1302_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_1303_ = l_List_head_x21___redArg(v___x_1302_, v_scopes_1301_);
    crate::leanh::lean_dec(v_scopes_1301_);
    v_opts_1304_ = crate::leanh::lean_ctor_get(v___x_1303_, 1);
    crate::leanh::lean_inc_ref(v_opts_1304_);
    crate::leanh::lean_dec(v___x_1303_);
    v___x_1305_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__2);
    v___x_1306_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___closed__5);
    v___x_1307_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1307_, 0, v_env_1299_);
    crate::leanh::lean_ctor_set(v___x_1307_, 1, v___x_1305_);
    crate::leanh::lean_ctor_set(v___x_1307_, 2, v___x_1306_);
    crate::leanh::lean_ctor_set(v___x_1307_, 3, v_opts_1304_);
    v___x_1308_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1307_);
    crate::leanh::lean_ctor_set(v___x_1308_, 1, v_msgData_1295_);
    v___x_1309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1309_, 0, v___x_1308_);
    return v___x_1309_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg___boxed(
    mut v_msgData_1310_: *mut crate::leanh::LeanObject,
    mut v___y_1311_: *mut crate::leanh::LeanObject,
    mut v___y_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg(v_msgData_1310_, v___y_1311_);
    crate::leanh::lean_dec(v___y_1311_);
    return v_res_1313_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__0()
-> f64 {
    let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1315_: f64 = 0.0;
    v___x_1314_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1315_ = lean_float_of_nat(v___x_1314_);
    return v___x_1315_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8(
    mut v_cls_1319_: *mut crate::leanh::LeanObject,
    mut v_msg_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
    mut v___y_1322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1330_: u8 = 0;
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1345_: u8 = 0;
    let mut v_tid_1346_: u64 = 0;
    let mut v_traces_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1350_: u8 = 0;
    let mut v___x_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: f64 = 0.0;
    let mut v___x_1353_: u8 = 0;
    let mut v___x_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1371_: u8 = 0;
    let mut v_isSharedCheck_1372_: u8 = 0;
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_a_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1324_ = l_Lean_Elab_Command_getRef___redArg(v___y_1321_);
                if crate::leanh::lean_obj_tag(v___x_1324_) == 0 {
                    v_a_1325_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                    crate::leanh::lean_inc(v_a_1325_);
                    crate::leanh::lean_dec_ref_known(v___x_1324_, 1);
                    v___x_1326_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg(v_msg_1320_, v___y_1322_);
                    v_a_1327_ = crate::leanh::lean_ctor_get(v___x_1326_, 0);
                    v_isSharedCheck_1373_ = (!crate::leanh::lean_is_exclusive(v___x_1326_)) as u8;
                    if v_isSharedCheck_1373_ == 0 {
                        v___x_1329_ = v___x_1326_;
                        v_isShared_1330_ = v_isSharedCheck_1373_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1327_);
                        crate::leanh::lean_dec(v___x_1326_);
                        v___x_1329_ = crate::leanh::lean_box(0);
                        v_isShared_1330_ = v_isSharedCheck_1373_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1320_);
                    crate::leanh::lean_dec(v_cls_1319_);
                    v_a_1374_ = crate::leanh::lean_ctor_get(v___x_1324_, 0);
                    v_isSharedCheck_1381_ = (!crate::leanh::lean_is_exclusive(v___x_1324_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1376_ = v___x_1324_;
                        v_isShared_1377_ = v_isSharedCheck_1381_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1374_);
                        crate::leanh::lean_dec(v___x_1324_);
                        v___x_1376_ = crate::leanh::lean_box(0);
                        v_isShared_1377_ = v_isSharedCheck_1381_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1331_ = lean_st_ref_take(v___y_1322_);
                v_traceState_1332_ = crate::leanh::lean_ctor_get(v___x_1331_, 9);
                v_env_1333_ = crate::leanh::lean_ctor_get(v___x_1331_, 0);
                v_messages_1334_ = crate::leanh::lean_ctor_get(v___x_1331_, 1);
                v_scopes_1335_ = crate::leanh::lean_ctor_get(v___x_1331_, 2);
                v_usedQuotCtxts_1336_ = crate::leanh::lean_ctor_get(v___x_1331_, 3);
                v_nextMacroScope_1337_ = crate::leanh::lean_ctor_get(v___x_1331_, 4);
                v_maxRecDepth_1338_ = crate::leanh::lean_ctor_get(v___x_1331_, 5);
                v_ngen_1339_ = crate::leanh::lean_ctor_get(v___x_1331_, 6);
                v_auxDeclNGen_1340_ = crate::leanh::lean_ctor_get(v___x_1331_, 7);
                v_infoState_1341_ = crate::leanh::lean_ctor_get(v___x_1331_, 8);
                v_snapshotTasks_1342_ = crate::leanh::lean_ctor_get(v___x_1331_, 10);
                v_isSharedCheck_1372_ = (!crate::leanh::lean_is_exclusive(v___x_1331_)) as u8;
                if v_isSharedCheck_1372_ == 0 {
                    v___x_1344_ = v___x_1331_;
                    v_isShared_1345_ = v_isSharedCheck_1372_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1342_);
                    crate::leanh::lean_inc(v_traceState_1332_);
                    crate::leanh::lean_inc(v_infoState_1341_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1340_);
                    crate::leanh::lean_inc(v_ngen_1339_);
                    crate::leanh::lean_inc(v_maxRecDepth_1338_);
                    crate::leanh::lean_inc(v_nextMacroScope_1337_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1336_);
                    crate::leanh::lean_inc(v_scopes_1335_);
                    crate::leanh::lean_inc(v_messages_1334_);
                    crate::leanh::lean_inc(v_env_1333_);
                    crate::leanh::lean_dec(v___x_1331_);
                    v___x_1344_ = crate::leanh::lean_box(0);
                    v_isShared_1345_ = v_isSharedCheck_1372_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_1346_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_1332_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_1347_ = crate::leanh::lean_ctor_get(v_traceState_1332_, 0);
                v_isSharedCheck_1371_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_1332_)) as u8;
                if v_isSharedCheck_1371_ == 0 {
                    v___x_1349_ = v_traceState_1332_;
                    v_isShared_1350_ = v_isSharedCheck_1371_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_1347_);
                    crate::leanh::lean_dec(v_traceState_1332_);
                    v___x_1349_ = crate::leanh::lean_box(0);
                    v_isShared_1350_ = v_isSharedCheck_1371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1351_ = crate::leanh::lean_box(0);
                v___x_1352_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__0_once), _init_l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__0);
                v___x_1353_ = 0;
                v___x_1354_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__1;
                v___x_1355_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_1355_, 0, v_cls_1319_);
                crate::leanh::lean_ctor_set(v___x_1355_, 1, v___x_1351_);
                crate::leanh::lean_ctor_set(v___x_1355_, 2, v___x_1354_);
                crate::leanh::lean_ctor_set_float(
                    v___x_1355_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_1352_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_1355_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_1352_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1355_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_1353_,
                );
                v___x_1356_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__2;
                v___x_1357_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1357_, 0, v___x_1355_);
                crate::leanh::lean_ctor_set(v___x_1357_, 1, v_a_1327_);
                crate::leanh::lean_ctor_set(v___x_1357_, 2, v___x_1356_);
                v___x_1358_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1358_, 0, v_a_1325_);
                crate::leanh::lean_ctor_set(v___x_1358_, 1, v___x_1357_);
                v___x_1359_ = l_Lean_PersistentArray_push___redArg(v_traces_1347_, v___x_1358_);
                if v_isShared_1350_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1349_, 0, v___x_1359_);
                    v___x_1361_ = v___x_1349_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1370_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1359_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_1370_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_1346_,
                    );
                    v___x_1361_ = v_reuseFailAlloc_1370_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1345_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1344_, 9, v___x_1361_);
                    v___x_1363_ = v___x_1344_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1369_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_env_1333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_messages_1334_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_scopes_1335_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_usedQuotCtxts_1336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_nextMacroScope_1337_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 5, v_maxRecDepth_1338_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 6, v_ngen_1339_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 7, v_auxDeclNGen_1340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 8, v_infoState_1341_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 9, v___x_1361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1369_, 10, v_snapshotTasks_1342_);
                    v___x_1363_ = v_reuseFailAlloc_1369_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1364_ = lean_st_ref_set(v___y_1322_, v___x_1363_);
                v___x_1365_ = crate::leanh::lean_box(0);
                if v_isShared_1330_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1329_, 0, v___x_1365_);
                    v___x_1367_ = v___x_1329_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1368_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1365_);
                    v___x_1367_ = v_reuseFailAlloc_1368_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1367_;
            }
            7 => {
                if v_isShared_1377_ == 0 {
                    v___x_1379_ = v___x_1376_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___boxed(
    mut v_cls_1382_: *mut crate::leanh::LeanObject,
    mut v_msg_1383_: *mut crate::leanh::LeanObject,
    mut v___y_1384_: *mut crate::leanh::LeanObject,
    mut v___y_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1387_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8(v_cls_1382_, v_msg_1383_, v___y_1384_, v___y_1385_);
    crate::leanh::lean_dec(v___y_1385_);
    crate::leanh::lean_dec_ref(v___y_1384_);
    return v_res_1387_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1390_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__1;
    v___x_1391_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__0;
    v___x_1392_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1391_,
        v___x_1390_,
    );
    return v___x_1392_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__5;
    v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
    return v___x_1398_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1400_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__7;
    v___x_1401_ = l_Lean_stringToMessageData(v___x_1400_);
    return v___x_1401_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1402_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8___closed__1;
    v___x_1403_ = l_Lean_stringToMessageData(v___x_1402_);
    return v___x_1403_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_1407_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__4;
    v___x_1408_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__11;
    v___x_1409_ = l_Lean_Name_append(v___x_1408_, v_cls_1407_);
    return v___x_1409_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__13;
    v___x_1412_ = l_Lean_stringToMessageData(v___x_1411_);
    return v___x_1412_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1414_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__15;
    v___x_1415_ = l_Lean_stringToMessageData(v___x_1414_);
    return v___x_1415_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4(
    mut v_mod_1420_: *mut crate::leanh::LeanObject,
    mut v_isMeta_1421_: u8,
    mut v_hint_1422_: *mut crate::leanh::LeanObject,
    mut v___y_1423_: *mut crate::leanh::LeanObject,
    mut v___y_1424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1453_: u8 = 0;
    let mut v_asyncMode_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1462_: u8 = 0;
    let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: u8 = 0;
    let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1472_: u8 = 0;
    let mut v_cls_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: u8 = 0;
    let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: u8 = 0;
    let mut v___x_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1426_ = lean_st_ref_get(v___y_1424_);
                v_env_1427_ = crate::leanh::lean_ctor_get(v___x_1426_, 0);
                crate::leanh::lean_inc_ref(v_env_1427_);
                crate::leanh::lean_dec(v___x_1426_);
                v_isExporting_1428_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_1427_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_1427_);
                v___x_1429_ = lean_st_ref_get(v___y_1424_);
                v_env_1430_ = crate::leanh::lean_ctor_get(v___x_1429_, 0);
                crate::leanh::lean_inc_ref(v_env_1430_);
                crate::leanh::lean_dec(v___x_1429_);
                v___x_1431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__2);
                crate::leanh::lean_inc(v_mod_1420_);
                v_entry_1432_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_1432_, 0, v_mod_1420_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_1432_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_1428_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_1432_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_1421_,
                );
                v___x_1433_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_1434_ = crate::leanh::lean_box(1);
                v___x_1435_ = crate::leanh::lean_box(0);
                v___x_1463_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_1431_,
                    v___x_1433_,
                    v_env_1430_,
                    v___x_1434_,
                    v___x_1435_,
                );
                v___x_1464_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7___redArg(v___x_1463_, v_entry_1432_);
                crate::leanh::lean_dec(v___x_1463_);
                if v___x_1464_ == 0 {
                    v___x_1465_ = l_Lean_inheritedTraceOptions;
                    v___x_1466_ = lean_st_ref_get(v___x_1465_);
                    v___x_1467_ = lean_st_ref_get(v___y_1424_);
                    v_scopes_1468_ = crate::leanh::lean_ctor_get(v___x_1467_, 2);
                    crate::leanh::lean_inc(v_scopes_1468_);
                    crate::leanh::lean_dec(v___x_1467_);
                    v___x_1469_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_1470_ = l_List_head_x21___redArg(v___x_1469_, v_scopes_1468_);
                    crate::leanh::lean_dec(v_scopes_1468_);
                    v_opts_1471_ = crate::leanh::lean_ctor_get(v___x_1470_, 1);
                    crate::leanh::lean_inc_ref(v_opts_1471_);
                    crate::leanh::lean_dec(v___x_1470_);
                    v_hasTrace_1472_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_1471_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_1472_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_1471_);
                        crate::leanh::lean_dec(v___x_1466_);
                        crate::leanh::lean_dec(v_hint_1422_);
                        crate::leanh::lean_dec(v_mod_1420_);
                        v___y_1437_ = v___y_1424_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_1473_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__4;
                        v___x_1493_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__12);
                        v___x_1494_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_1466_,
                            v_opts_1471_,
                            v___x_1493_,
                        );
                        crate::leanh::lean_dec_ref(v_opts_1471_);
                        crate::leanh::lean_dec(v___x_1466_);
                        if v___x_1494_ == 0 {
                            crate::leanh::lean_dec(v_hint_1422_);
                            crate::leanh::lean_dec(v_mod_1420_);
                            v___y_1437_ = v___y_1424_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1495_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__14);
                            if v_isExporting_1428_ == 0 {
                                v___x_1504_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__19;
                                v___y_1497_ = v___x_1504_;
                                state = 6;
                                continue;
                            } else {
                                v___x_1505_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__20;
                                v___y_1497_ = v___x_1505_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_1432_, 1);
                    crate::leanh::lean_dec(v_hint_1422_);
                    crate::leanh::lean_dec(v_mod_1420_);
                    v___x_1506_ = crate::leanh::lean_box(0);
                    v___x_1507_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1507_, 0, v___x_1506_);
                    return v___x_1507_;
                }
            }
            1 => {
                v___x_1438_ = lean_st_ref_take(v___y_1437_);
                v_toEnvExtension_1439_ = crate::leanh::lean_ctor_get(v___x_1433_, 0);
                v_env_1440_ = crate::leanh::lean_ctor_get(v___x_1438_, 0);
                v_messages_1441_ = crate::leanh::lean_ctor_get(v___x_1438_, 1);
                v_scopes_1442_ = crate::leanh::lean_ctor_get(v___x_1438_, 2);
                v_usedQuotCtxts_1443_ = crate::leanh::lean_ctor_get(v___x_1438_, 3);
                v_nextMacroScope_1444_ = crate::leanh::lean_ctor_get(v___x_1438_, 4);
                v_maxRecDepth_1445_ = crate::leanh::lean_ctor_get(v___x_1438_, 5);
                v_ngen_1446_ = crate::leanh::lean_ctor_get(v___x_1438_, 6);
                v_auxDeclNGen_1447_ = crate::leanh::lean_ctor_get(v___x_1438_, 7);
                v_infoState_1448_ = crate::leanh::lean_ctor_get(v___x_1438_, 8);
                v_traceState_1449_ = crate::leanh::lean_ctor_get(v___x_1438_, 9);
                v_snapshotTasks_1450_ = crate::leanh::lean_ctor_get(v___x_1438_, 10);
                v_isSharedCheck_1462_ = (!crate::leanh::lean_is_exclusive(v___x_1438_)) as u8;
                if v_isSharedCheck_1462_ == 0 {
                    v___x_1452_ = v___x_1438_;
                    v_isShared_1453_ = v_isSharedCheck_1462_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1450_);
                    crate::leanh::lean_inc(v_traceState_1449_);
                    crate::leanh::lean_inc(v_infoState_1448_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1447_);
                    crate::leanh::lean_inc(v_ngen_1446_);
                    crate::leanh::lean_inc(v_maxRecDepth_1445_);
                    crate::leanh::lean_inc(v_nextMacroScope_1444_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1443_);
                    crate::leanh::lean_inc(v_scopes_1442_);
                    crate::leanh::lean_inc(v_messages_1441_);
                    crate::leanh::lean_inc(v_env_1440_);
                    crate::leanh::lean_dec(v___x_1438_);
                    v___x_1452_ = crate::leanh::lean_box(0);
                    v_isShared_1453_ = v_isSharedCheck_1462_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_1454_ = crate::leanh::lean_ctor_get(v_toEnvExtension_1439_, 2);
                v___x_1455_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_1433_,
                    v_env_1440_,
                    v_entry_1432_,
                    v_asyncMode_1454_,
                    v___x_1435_,
                );
                if v_isShared_1453_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1452_, 0, v___x_1455_);
                    v___x_1457_ = v___x_1452_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1461_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 1, v_messages_1441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 2, v_scopes_1442_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 3, v_usedQuotCtxts_1443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 4, v_nextMacroScope_1444_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 5, v_maxRecDepth_1445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 6, v_ngen_1446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 7, v_auxDeclNGen_1447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 8, v_infoState_1448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 9, v_traceState_1449_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1461_, 10, v_snapshotTasks_1450_);
                    v___x_1457_ = v_reuseFailAlloc_1461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1458_ = lean_st_ref_set(v___y_1437_, v___x_1457_);
                v___x_1459_ = crate::leanh::lean_box(0);
                v___x_1460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1459_);
                return v___x_1460_;
            }
            4 => {
                v___x_1477_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1477_, 0, v___y_1475_);
                crate::leanh::lean_ctor_set(v___x_1477_, 1, v___y_1476_);
                v___x_1478_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__8(v_cls_1473_, v___x_1477_, v___y_1423_, v___y_1424_);
                if crate::leanh::lean_obj_tag(v___x_1478_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1478_, 1);
                    v___y_1437_ = v___y_1424_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_1432_, 1);
                    return v___x_1478_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_1481_);
                v___x_1482_ = l_Lean_stringToMessageData(v___y_1481_);
                v___x_1483_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1483_, 0, v___y_1480_);
                crate::leanh::lean_ctor_set(v___x_1483_, 1, v___x_1482_);
                v___x_1484_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__6);
                v___x_1485_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1485_, 0, v___x_1483_);
                crate::leanh::lean_ctor_set(v___x_1485_, 1, v___x_1484_);
                v___x_1486_ = l_Lean_MessageData_ofName(v_mod_1420_);
                v___x_1487_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1487_, 0, v___x_1485_);
                crate::leanh::lean_ctor_set(v___x_1487_, 1, v___x_1486_);
                v___x_1488_ = l_Lean_Name_isAnonymous(v_hint_1422_);
                if v___x_1488_ == 0 {
                    v___x_1489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__8);
                    v___x_1490_ = l_Lean_MessageData_ofName(v_hint_1422_);
                    v___x_1491_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1491_, 0, v___x_1489_);
                    crate::leanh::lean_ctor_set(v___x_1491_, 1, v___x_1490_);
                    v___y_1475_ = v___x_1487_;
                    v___y_1476_ = v___x_1491_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_1422_);
                    v___x_1492_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__9);
                    v___y_1475_ = v___x_1487_;
                    v___y_1476_ = v___x_1492_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_1497_);
                v___x_1498_ = l_Lean_stringToMessageData(v___y_1497_);
                v___x_1499_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1499_, 0, v___x_1495_);
                crate::leanh::lean_ctor_set(v___x_1499_, 1, v___x_1498_);
                v___x_1500_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__16);
                v___x_1501_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1499_);
                crate::leanh::lean_ctor_set(v___x_1501_, 1, v___x_1500_);
                if v_isMeta_1421_ == 0 {
                    v___x_1502_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__17;
                    v___y_1480_ = v___x_1501_;
                    v___y_1481_ = v___x_1502_;
                    state = 5;
                    continue;
                } else {
                    v___x_1503_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___closed__18;
                    v___y_1480_ = v___x_1501_;
                    v___y_1481_ = v___x_1503_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4___boxed(
    mut v_mod_1508_: *mut crate::leanh::LeanObject,
    mut v_isMeta_1509_: *mut crate::leanh::LeanObject,
    mut v_hint_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
    mut v___y_1512_: *mut crate::leanh::LeanObject,
    mut v___y_1513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_1514_: u8 = 0;
    let mut v_res_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_1514_ = (crate::leanh::lean_unbox(v_isMeta_1509_) as u8);
    v_res_1515_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4(v_mod_1508_, v_isMeta_boxed_1514_, v_hint_1510_, v___y_1511_, v___y_1512_);
    crate::leanh::lean_dec(v___y_1512_);
    crate::leanh::lean_dec_ref(v___y_1511_);
    return v_res_1515_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__5(
    mut v___x_1516_: *mut crate::leanh::LeanObject,
    mut v_declName_1517_: *mut crate::leanh::LeanObject,
    mut v_as_1518_: *mut crate::leanh::LeanObject,
    mut v_sz_1519_: usize,
    mut v_i_1520_: usize,
    mut v_b_1521_: *mut crate::leanh::LeanObject,
    mut v___y_1522_: *mut crate::leanh::LeanObject,
    mut v___y_1523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1525_: u8 = 0;
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: u8 = 0;
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1525_ = lean_usize_dec_lt(v_i_1520_, v_sz_1519_);
                if v___x_1525_ == 0 {
                    crate::leanh::lean_dec(v_declName_1517_);
                    v___x_1526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1526_, 0, v_b_1521_);
                    return v___x_1526_;
                } else {
                    v___x_1527_ = l_Lean_Environment_header(v___x_1516_);
                    v_modules_1528_ = crate::leanh::lean_ctor_get(v___x_1527_, 3);
                    crate::leanh::lean_inc_ref(v_modules_1528_);
                    crate::leanh::lean_dec_ref(v___x_1527_);
                    v___x_1529_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_1530_ = lean_array_uget_borrowed(v_as_1518_, v_i_1520_);
                    v___x_1531_ = lean_array_get(v___x_1529_, v_modules_1528_, v_a_1530_);
                    crate::leanh::lean_dec_ref(v_modules_1528_);
                    v_toImport_1532_ = crate::leanh::lean_ctor_get(v___x_1531_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_1532_);
                    crate::leanh::lean_dec(v___x_1531_);
                    v_module_1533_ = crate::leanh::lean_ctor_get(v_toImport_1532_, 0);
                    crate::leanh::lean_inc(v_module_1533_);
                    crate::leanh::lean_dec_ref(v_toImport_1532_);
                    v___x_1534_ = 0;
                    crate::leanh::lean_inc(v_declName_1517_);
                    v___x_1535_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4(v_module_1533_, v___x_1534_, v_declName_1517_, v___y_1522_, v___y_1523_);
                    if crate::leanh::lean_obj_tag(v___x_1535_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1535_, 1);
                        v___x_1536_ = crate::leanh::lean_box(0);
                        v___x_1537_ = 1usize;
                        v___x_1538_ = lean_usize_add(v_i_1520_, v___x_1537_);
                        v_i_1520_ = v___x_1538_;
                        v_b_1521_ = v___x_1536_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_1517_);
                        return v___x_1535_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__5___boxed(
    mut v___x_1540_: *mut crate::leanh::LeanObject,
    mut v_declName_1541_: *mut crate::leanh::LeanObject,
    mut v_as_1542_: *mut crate::leanh::LeanObject,
    mut v_sz_1543_: *mut crate::leanh::LeanObject,
    mut v_i_1544_: *mut crate::leanh::LeanObject,
    mut v_b_1545_: *mut crate::leanh::LeanObject,
    mut v___y_1546_: *mut crate::leanh::LeanObject,
    mut v___y_1547_: *mut crate::leanh::LeanObject,
    mut v___y_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1549_: usize = 0;
    let mut v_i_boxed_1550_: usize = 0;
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1549_ = crate::leanh::lean_unbox_usize(v_sz_1543_);
    crate::leanh::lean_dec(v_sz_1543_);
    v_i_boxed_1550_ = crate::leanh::lean_unbox_usize(v_i_1544_);
    crate::leanh::lean_dec(v_i_1544_);
    v_res_1551_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__5(v___x_1540_, v_declName_1541_, v_as_1542_, v_sz_boxed_1549_, v_i_boxed_1550_, v_b_1545_, v___y_1546_, v___y_1547_);
    crate::leanh::lean_dec(v___y_1547_);
    crate::leanh::lean_dec_ref(v___y_1546_);
    crate::leanh::lean_dec_ref(v_as_1542_);
    crate::leanh::lean_dec_ref(v___x_1540_);
    return v_res_1551_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__1;
    v___x_1555_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__0;
    v___x_1556_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1555_,
        v___x_1554_,
    );
    return v___x_1556_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(
    mut v_declName_1559_: *mut crate::leanh::LeanObject,
    mut v_isMeta_1560_: u8,
    mut v___y_1561_: *mut crate::leanh::LeanObject,
    mut v___y_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1572_: usize = 0;
    let mut v___x_1573_: usize = 0;
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1581_: u8 = 0;
    let mut v_unused_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: u8 = 0;
    let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1594_: u8 = 0;
    let mut v_toImport_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1605_: u8 = 0;
    let mut v___x_1606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1564_ = lean_st_ref_get(v___y_1562_);
                v_env_1568_ = crate::leanh::lean_ctor_get(v___x_1564_, 0);
                crate::leanh::lean_inc_ref(v_env_1568_);
                crate::leanh::lean_dec(v___x_1564_);
                v___x_1583_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1568_, v_declName_1559_);
                if crate::leanh::lean_obj_tag(v___x_1583_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_1568_);
                    crate::leanh::lean_dec(v_declName_1559_);
                    state = 1;
                    continue;
                } else {
                    v_val_1584_ = crate::leanh::lean_ctor_get(v___x_1583_, 0);
                    crate::leanh::lean_inc(v_val_1584_);
                    crate::leanh::lean_dec_ref_known(v___x_1583_, 1);
                    v___x_1585_ = l_Lean_Environment_header(v_env_1568_);
                    v_modules_1586_ = crate::leanh::lean_ctor_get(v___x_1585_, 3);
                    crate::leanh::lean_inc_ref(v_modules_1586_);
                    crate::leanh::lean_dec_ref(v___x_1585_);
                    v___x_1587_ = lean_array_get_size(v_modules_1586_);
                    v___x_1588_ = lean_nat_dec_lt(v_val_1584_, v___x_1587_);
                    if v___x_1588_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_1586_);
                        crate::leanh::lean_dec(v_val_1584_);
                        crate::leanh::lean_dec_ref(v_env_1568_);
                        crate::leanh::lean_dec(v_declName_1559_);
                        state = 1;
                        continue;
                    } else {
                        v___x_1589_ = lean_st_ref_get(v___y_1562_);
                        v_env_1590_ = crate::leanh::lean_ctor_get(v___x_1589_, 0);
                        crate::leanh::lean_inc_ref(v_env_1590_);
                        crate::leanh::lean_dec(v___x_1589_);
                        v___x_1591_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__2);
                        v___x_1592_ = lean_array_fget(v_modules_1586_, v_val_1584_);
                        crate::leanh::lean_dec(v_val_1584_);
                        crate::leanh::lean_dec_ref(v_modules_1586_);
                        if v_isMeta_1560_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_1590_);
                            v___y_1594_ = v_isMeta_1560_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_1559_);
                            v___x_1605_ = l_Lean_isMarkedMeta(v_env_1590_, v_declName_1559_);
                            if v___x_1605_ == 0 {
                                v___y_1594_ = v_isMeta_1560_;
                                state = 5;
                                continue;
                            } else {
                                v___x_1606_ = 0;
                                v___y_1594_ = v___x_1606_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1566_ = crate::leanh::lean_box(0);
                v___x_1567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1567_, 0, v___x_1566_);
                return v___x_1567_;
            }
            2 => {
                v___x_1571_ = crate::leanh::lean_box(0);
                v_sz_1572_ = lean_array_size(v___y_1570_);
                v___x_1573_ = 0usize;
                v___x_1574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__5(v_env_1568_, v_declName_1559_, v___y_1570_, v_sz_1572_, v___x_1573_, v___x_1571_, v___y_1561_, v___y_1562_);
                crate::leanh::lean_dec_ref(v___y_1570_);
                crate::leanh::lean_dec_ref(v_env_1568_);
                if crate::leanh::lean_obj_tag(v___x_1574_) == 0 {
                    v_isSharedCheck_1581_ = (!crate::leanh::lean_is_exclusive(v___x_1574_)) as u8;
                    if v_isSharedCheck_1581_ == 0 {
                        v_unused_1582_ = crate::leanh::lean_ctor_get(v___x_1574_, 0);
                        crate::leanh::lean_dec(v_unused_1582_);
                        v___x_1576_ = v___x_1574_;
                        v_isShared_1577_ = v_isSharedCheck_1581_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1574_);
                        v___x_1576_ = crate::leanh::lean_box(0);
                        v_isShared_1577_ = v_isSharedCheck_1581_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_1574_;
                }
            }
            3 => {
                if v_isShared_1577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1576_, 0, v___x_1571_);
                    v___x_1579_ = v___x_1576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1580_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1580_, 0, v___x_1571_);
                    v___x_1579_ = v_reuseFailAlloc_1580_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1579_;
            }
            5 => {
                v_toImport_1595_ = crate::leanh::lean_ctor_get(v___x_1592_, 0);
                crate::leanh::lean_inc_ref(v_toImport_1595_);
                crate::leanh::lean_dec(v___x_1592_);
                v_module_1596_ = crate::leanh::lean_ctor_get(v_toImport_1595_, 0);
                crate::leanh::lean_inc(v_module_1596_);
                crate::leanh::lean_dec_ref(v_toImport_1595_);
                crate::leanh::lean_inc(v_declName_1559_);
                v___x_1597_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4(v_module_1596_, v___y_1594_, v_declName_1559_, v___y_1561_, v___y_1562_);
                if crate::leanh::lean_obj_tag(v___x_1597_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1597_, 1);
                    v___x_1598_ = l_Lean_indirectModUseExt;
                    v___x_1599_ = crate::leanh::lean_box(1);
                    v___x_1600_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_1568_);
                    v___x_1601_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_1591_,
                        v___x_1598_,
                        v_env_1568_,
                        v___x_1599_,
                        v___x_1600_,
                    );
                    v___x_1602_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg(v___x_1601_, v_declName_1559_);
                    crate::leanh::lean_dec(v___x_1601_);
                    if crate::leanh::lean_obj_tag(v___x_1602_) == 0 {
                        v___x_1603_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___closed__3;
                        v___y_1570_ = v___x_1603_;
                        state = 2;
                        continue;
                    } else {
                        v_val_1604_ = crate::leanh::lean_ctor_get(v___x_1602_, 0);
                        crate::leanh::lean_inc(v_val_1604_);
                        crate::leanh::lean_dec_ref_known(v___x_1602_, 1);
                        v___y_1570_ = v_val_1604_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1568_);
                    crate::leanh::lean_dec(v_declName_1559_);
                    return v___x_1597_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___boxed(
    mut v_declName_1607_: *mut crate::leanh::LeanObject,
    mut v_isMeta_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
    mut v___y_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_1612_: u8 = 0;
    let mut v_res_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_1612_ = (crate::leanh::lean_unbox(v_isMeta_1608_) as u8);
    v_res_1613_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(v_declName_1607_, v_isMeta_boxed_1612_, v___y_1609_, v___y_1610_);
    crate::leanh::lean_dec(v___y_1610_);
    crate::leanh::lean_dec_ref(v___y_1609_);
    return v_res_1613_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__4(
    mut v_as_1614_: *mut crate::leanh::LeanObject,
    mut v_i_1615_: usize,
    mut v_stop_1616_: usize,
    mut v_b_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
    mut v___y_1619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1621_: u8 = 0;
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: usize = 0;
    let mut v___x_1626_: usize = 0;
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1621_ = lean_usize_dec_eq(v_i_1615_, v_stop_1616_);
                if v___x_1621_ == 0 {
                    v___x_1622_ = lean_array_uget_borrowed(v_as_1614_, v_i_1615_);
                    crate::leanh::lean_inc(v___x_1622_);
                    v___x_1623_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(v___x_1622_, v___x_1621_, v___y_1618_, v___y_1619_);
                    if crate::leanh::lean_obj_tag(v___x_1623_) == 0 {
                        v_a_1624_ = crate::leanh::lean_ctor_get(v___x_1623_, 0);
                        crate::leanh::lean_inc(v_a_1624_);
                        crate::leanh::lean_dec_ref_known(v___x_1623_, 1);
                        v___x_1625_ = 1usize;
                        v___x_1626_ = lean_usize_add(v_i_1615_, v___x_1625_);
                        v_i_1615_ = v___x_1626_;
                        v_b_1617_ = v_a_1624_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1623_;
                    }
                } else {
                    v___x_1628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1628_, 0, v_b_1617_);
                    return v___x_1628_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__4___boxed(
    mut v_as_1629_: *mut crate::leanh::LeanObject,
    mut v_i_1630_: *mut crate::leanh::LeanObject,
    mut v_stop_1631_: *mut crate::leanh::LeanObject,
    mut v_b_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_1636_: usize = 0;
    let mut v_stop_boxed_1637_: usize = 0;
    let mut v_res_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1636_ = crate::leanh::lean_unbox_usize(v_i_1630_);
    crate::leanh::lean_dec(v_i_1630_);
    v_stop_boxed_1637_ = crate::leanh::lean_unbox_usize(v_stop_1631_);
    crate::leanh::lean_dec(v_stop_1631_);
    v_res_1638_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__4(v_as_1629_, v_i_boxed_1636_, v_stop_boxed_1637_, v_b_1632_, v___y_1633_, v___y_1634_);
    crate::leanh::lean_dec(v___y_1634_);
    crate::leanh::lean_dec_ref(v___y_1633_);
    crate::leanh::lean_dec_ref(v_as_1629_);
    return v_res_1638_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1639_ = crate::leanh::lean_box(1);
    v___x_1640_ = l_Lean_MessageData_ofFormat(v___x_1639_);
    return v___x_1640_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__2;
    v___x_1645_ = l_Lean_MessageData_ofFormat(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3(
    mut v_x_1646_: *mut crate::leanh::LeanObject,
    mut v_x_1647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1652_: u8 = 0;
    let mut v_before_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v_unused_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1647_) == 0 {
                    return v_x_1646_;
                } else {
                    v_head_1648_ = crate::leanh::lean_ctor_get(v_x_1647_, 0);
                    v_tail_1649_ = crate::leanh::lean_ctor_get(v_x_1647_, 1);
                    v_isSharedCheck_1671_ = (!crate::leanh::lean_is_exclusive(v_x_1647_)) as u8;
                    if v_isSharedCheck_1671_ == 0 {
                        v___x_1651_ = v_x_1647_;
                        v_isShared_1652_ = v_isSharedCheck_1671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1649_);
                        crate::leanh::lean_inc(v_head_1648_);
                        crate::leanh::lean_dec(v_x_1647_);
                        v___x_1651_ = crate::leanh::lean_box(0);
                        v_isShared_1652_ = v_isSharedCheck_1671_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_1653_ = crate::leanh::lean_ctor_get(v_head_1648_, 0);
                v_isSharedCheck_1669_ = (!crate::leanh::lean_is_exclusive(v_head_1648_)) as u8;
                if v_isSharedCheck_1669_ == 0 {
                    v_unused_1670_ = crate::leanh::lean_ctor_get(v_head_1648_, 1);
                    crate::leanh::lean_dec(v_unused_1670_);
                    v___x_1655_ = v_head_1648_;
                    v_isShared_1656_ = v_isSharedCheck_1669_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_1653_);
                    crate::leanh::lean_dec(v_head_1648_);
                    v___x_1655_ = crate::leanh::lean_box(0);
                    v_isShared_1656_ = v_isSharedCheck_1669_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1657_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_1656_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1655_, 7);
                    crate::leanh::lean_ctor_set(v___x_1655_, 1, v___x_1657_);
                    crate::leanh::lean_ctor_set(v___x_1655_, 0, v_x_1646_);
                    v___x_1659_ = v___x_1655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1668_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_x_1646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1657_);
                    v___x_1659_ = v_reuseFailAlloc_1668_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1660_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__3);
                if v_isShared_1652_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1651_, 7);
                    crate::leanh::lean_ctor_set(v___x_1651_, 1, v___x_1660_);
                    crate::leanh::lean_ctor_set(v___x_1651_, 0, v___x_1659_);
                    v___x_1662_ = v___x_1651_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 1, v___x_1660_);
                    v___x_1662_ = v_reuseFailAlloc_1667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1663_ = l_Lean_MessageData_ofSyntax(v_before_1653_);
                v___x_1664_ = l_Lean_indentD(v___x_1663_);
                v___x_1665_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1665_, 0, v___x_1662_);
                crate::leanh::lean_ctor_set(v___x_1665_, 1, v___x_1664_);
                v_x_1646_ = v___x_1665_;
                v_x_1647_ = v_tail_1649_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__2(
    mut v_opts_1672_: *mut crate::leanh::LeanObject,
    mut v_opt_1673_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_1674_ = crate::leanh::lean_ctor_get(v_opt_1673_, 0);
    v_defValue_1675_ = crate::leanh::lean_ctor_get(v_opt_1673_, 1);
    v_map_1676_ = crate::leanh::lean_ctor_get(v_opts_1672_, 0);
    v___x_1677_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_1676_,
            v_name_1674_,
        );
    if crate::leanh::lean_obj_tag(v___x_1677_) == 0 {
        let mut v___x_1678_: u8 = 0;
        v___x_1678_ = (crate::leanh::lean_unbox(v_defValue_1675_) as u8);
        return v___x_1678_;
    } else {
        let mut v_val_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_1679_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
        crate::leanh::lean_inc(v_val_1679_);
        crate::leanh::lean_dec_ref_known(v___x_1677_, 1);
        if crate::leanh::lean_obj_tag(v_val_1679_) == 1 {
            let mut v_v_1680_: u8 = 0;
            v_v_1680_ = crate::leanh::lean_ctor_get_uint8(v_val_1679_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_1679_, 0);
            return v_v_1680_;
        } else {
            let mut v___x_1681_: u8 = 0;
            crate::leanh::lean_dec(v_val_1679_);
            v___x_1681_ = (crate::leanh::lean_unbox(v_defValue_1675_) as u8);
            return v___x_1681_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__2___boxed(
    mut v_opts_1682_: *mut crate::leanh::LeanObject,
    mut v_opt_1683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1684_: u8 = 0;
    let mut v_r_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__2(v_opts_1682_, v_opt_1683_);
    crate::leanh::lean_dec_ref(v_opt_1683_);
    crate::leanh::lean_dec_ref(v_opts_1682_);
    v_r_1685_ = crate::leanh::lean_box((v_res_1684_) as usize);
    return v_r_1685_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__1;
    v___x_1690_ = l_Lean_MessageData_ofFormat(v___x_1689_);
    return v___x_1690_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg(
    mut v_msgData_1691_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1701_: u8 = 0;
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_1705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1708_: u8 = 0;
    let mut v___x_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1720_: u8 = 0;
    let mut v_unused_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1695_ = lean_st_ref_get(v___y_1693_);
                v_scopes_1696_ = crate::leanh::lean_ctor_get(v___x_1695_, 2);
                crate::leanh::lean_inc(v_scopes_1696_);
                crate::leanh::lean_dec(v___x_1695_);
                v___x_1697_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_1698_ = l_List_head_x21___redArg(v___x_1697_, v_scopes_1696_);
                crate::leanh::lean_dec(v_scopes_1696_);
                v_opts_1699_ = crate::leanh::lean_ctor_get(v___x_1698_, 1);
                crate::leanh::lean_inc_ref(v_opts_1699_);
                crate::leanh::lean_dec(v___x_1698_);
                v___x_1700_ = l_Lean_Elab_pp_macroStack;
                v___x_1701_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__2(v_opts_1699_, v___x_1700_);
                crate::leanh::lean_dec_ref(v_opts_1699_);
                if v___x_1701_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_1692_);
                    v___x_1702_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1702_, 0, v_msgData_1691_);
                    return v___x_1702_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_1692_) == 0 {
                        v___x_1703_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1703_, 0, v_msgData_1691_);
                        return v___x_1703_;
                    } else {
                        v_head_1704_ = crate::leanh::lean_ctor_get(v_macroStack_1692_, 0);
                        crate::leanh::lean_inc(v_head_1704_);
                        v_after_1705_ = crate::leanh::lean_ctor_get(v_head_1704_, 1);
                        v_isSharedCheck_1720_ =
                            (!crate::leanh::lean_is_exclusive(v_head_1704_)) as u8;
                        if v_isSharedCheck_1720_ == 0 {
                            v_unused_1721_ = crate::leanh::lean_ctor_get(v_head_1704_, 0);
                            crate::leanh::lean_dec(v_unused_1721_);
                            v___x_1707_ = v_head_1704_;
                            v_isShared_1708_ = v_isSharedCheck_1720_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_1705_);
                            crate::leanh::lean_dec(v_head_1704_);
                            v___x_1707_ = crate::leanh::lean_box(0);
                            v_isShared_1708_ = v_isSharedCheck_1720_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1709_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3___closed__0);
                if v_isShared_1708_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1707_, 7);
                    crate::leanh::lean_ctor_set(v___x_1707_, 1, v___x_1709_);
                    crate::leanh::lean_ctor_set(v___x_1707_, 0, v_msgData_1691_);
                    v___x_1711_ = v___x_1707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1719_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 0, v_msgData_1691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1719_, 1, v___x_1709_);
                    v___x_1711_ = v_reuseFailAlloc_1719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___closed__2);
                v___x_1713_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1713_, 0, v___x_1711_);
                crate::leanh::lean_ctor_set(v___x_1713_, 1, v___x_1712_);
                v___x_1714_ = l_Lean_MessageData_ofSyntax(v_after_1705_);
                v___x_1715_ = l_Lean_indentD(v___x_1714_);
                v_msgData_1716_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_1716_, 0, v___x_1713_);
                crate::leanh::lean_ctor_set(v_msgData_1716_, 1, v___x_1715_);
                v___x_1717_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1_spec__3(v_msgData_1716_, v_macroStack_1692_);
                v___x_1718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1717_);
                return v___x_1718_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg___boxed(
    mut v_msgData_1722_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1723_: *mut crate::leanh::LeanObject,
    mut v___y_1724_: *mut crate::leanh::LeanObject,
    mut v___y_1725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg(v_msgData_1722_, v_macroStack_1723_, v___y_1724_);
    crate::leanh::lean_dec(v___y_1724_);
    return v_res_1726_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(
    mut v_msg_1727_: *mut crate::leanh::LeanObject,
    mut v___y_1728_: *mut crate::leanh::LeanObject,
    mut v___y_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1746_: u8 = 0;
    let mut v_a_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1750_: u8 = 0;
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1754_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1731_ = l_Lean_Elab_Command_getRef___redArg(v___y_1728_);
                if crate::leanh::lean_obj_tag(v___x_1731_) == 0 {
                    v_a_1732_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                    crate::leanh::lean_inc(v_a_1732_);
                    crate::leanh::lean_dec_ref_known(v___x_1731_, 1);
                    v_macroStack_1733_ = crate::leanh::lean_ctor_get(v___y_1728_, 4);
                    v___x_1734_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg(v_msg_1727_, v___y_1729_);
                    v_a_1735_ = crate::leanh::lean_ctor_get(v___x_1734_, 0);
                    crate::leanh::lean_inc(v_a_1735_);
                    crate::leanh::lean_dec_ref(v___x_1734_);
                    v___x_1736_ = l_Lean_Elab_getBetterRef(v_a_1732_, v_macroStack_1733_);
                    crate::leanh::lean_dec(v_a_1732_);
                    crate::leanh::lean_inc(v_macroStack_1733_);
                    v___x_1737_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg(v_a_1735_, v_macroStack_1733_, v___y_1729_);
                    v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1737_, 0);
                    v_isSharedCheck_1746_ = (!crate::leanh::lean_is_exclusive(v___x_1737_)) as u8;
                    if v_isSharedCheck_1746_ == 0 {
                        v___x_1740_ = v___x_1737_;
                        v_isShared_1741_ = v_isSharedCheck_1746_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1738_);
                        crate::leanh::lean_dec(v___x_1737_);
                        v___x_1740_ = crate::leanh::lean_box(0);
                        v_isShared_1741_ = v_isSharedCheck_1746_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_1727_);
                    v_a_1747_ = crate::leanh::lean_ctor_get(v___x_1731_, 0);
                    v_isSharedCheck_1754_ = (!crate::leanh::lean_is_exclusive(v___x_1731_)) as u8;
                    if v_isSharedCheck_1754_ == 0 {
                        v___x_1749_ = v___x_1731_;
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1747_);
                        crate::leanh::lean_dec(v___x_1731_);
                        v___x_1749_ = crate::leanh::lean_box(0);
                        v_isShared_1750_ = v_isSharedCheck_1754_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1742_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1742_, 0, v___x_1736_);
                crate::leanh::lean_ctor_set(v___x_1742_, 1, v_a_1738_);
                if v_isShared_1741_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1740_, 1);
                    crate::leanh::lean_ctor_set(v___x_1740_, 0, v___x_1742_);
                    v___x_1744_ = v___x_1740_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1742_);
                    v___x_1744_ = v_reuseFailAlloc_1745_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1744_;
            }
            3 => {
                if v_isShared_1750_ == 0 {
                    v___x_1752_ = v___x_1749_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
                    v___x_1752_ = v_reuseFailAlloc_1753_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1752_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg___boxed(
    mut v_msg_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1759_ =
        l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(
            v_msg_1755_,
            v___y_1756_,
            v___y_1757_,
        );
    crate::leanh::lean_dec(v___y_1757_);
    crate::leanh::lean_dec_ref(v___y_1756_);
    return v_res_1759_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1770_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__5;
    v___x_1771_ = l_Lean_stringToMessageData(v___x_1770_);
    return v___x_1771_;
}
pub unsafe fn l_Lean_Elab_Term_Doc_elabRecommendedSpelling(
    mut v_x_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1818_: u8 = 0;
    let mut v___y_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut v___y_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1845_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1856_: usize = 0;
    let mut v___x_1857_: usize = 0;
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1862_: usize = 0;
    let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: u8 = 0;
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: u8 = 0;
    let mut v___x_1872_: usize = 0;
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: usize = 0;
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1879_: u8 = 0;
    let mut v___x_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1883_: u8 = 0;
    let mut v_docs_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_spelling_1889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: u8 = 0;
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_notation_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: u8 = 0;
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: u8 = 0;
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1908_: usize = 0;
    let mut v___x_1909_: usize = 0;
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: usize = 0;
    let mut v___x_1913_: usize = 0;
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: u8 = 0;
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: u8 = 0;
    let mut v___x_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_docs_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1844_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4;
                crate::leanh::lean_inc(v_x_1785_);
                v___x_1845_ = l_Lean_Syntax_isOfKind(v_x_1785_, v___x_1844_);
                if v___x_1845_ == 0 {
                    crate::leanh::lean_dec(v_x_1785_);
                    v___x_1846_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once
                        ),
                        _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6,
                    );
                    v___x_1847_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(v___x_1846_, v_a_1786_, v_a_1787_);
                    return v___x_1847_;
                } else {
                    v___x_1848_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1916_ = l_Lean_Syntax_getArg(v_x_1785_, v___x_1848_);
                    v___x_1917_ = l_Lean_Syntax_isNone(v___x_1916_);
                    if v___x_1917_ == 0 {
                        v___x_1918_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_1916_);
                        v___x_1919_ = l_Lean_Syntax_matchesNull(v___x_1916_, v___x_1918_);
                        if v___x_1919_ == 0 {
                            crate::leanh::lean_dec(v___x_1916_);
                            crate::leanh::lean_dec(v_x_1785_);
                            v___x_1920_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once
                                ),
                                _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6,
                            );
                            v___x_1921_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(v___x_1920_, v_a_1786_, v_a_1787_);
                            return v___x_1921_;
                        } else {
                            v_docs_1922_ = l_Lean_Syntax_getArg(v___x_1916_, v___x_1848_);
                            crate::leanh::lean_dec(v___x_1916_);
                            v___x_1923_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__11;
                            crate::leanh::lean_inc(v_docs_1922_);
                            v___x_1924_ = l_Lean_Syntax_isOfKind(v_docs_1922_, v___x_1923_);
                            if v___x_1924_ == 0 {
                                crate::leanh::lean_dec(v_docs_1922_);
                                crate::leanh::lean_dec(v_x_1785_);
                                v___x_1925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6), core::ptr::addr_of_mut!(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once), _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6);
                                v___x_1926_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(v___x_1925_, v_a_1786_, v_a_1787_);
                                return v___x_1926_;
                            } else {
                                v___x_1927_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1927_, 0, v_docs_1922_);
                                v_docs_1885_ = v___x_1927_;
                                v___y_1886_ = v_a_1786_;
                                v___y_1887_ = v_a_1787_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1916_);
                        v___x_1928_ = crate::leanh::lean_box(0);
                        v_docs_1885_ = v___x_1928_;
                        v___y_1886_ = v_a_1786_;
                        v___y_1887_ = v_a_1787_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1795_ = lean_st_ref_take(v___y_1792_);
                v_env_1796_ = crate::leanh::lean_ctor_get(v___x_1795_, 0);
                v_messages_1797_ = crate::leanh::lean_ctor_get(v___x_1795_, 1);
                v_scopes_1798_ = crate::leanh::lean_ctor_get(v___x_1795_, 2);
                v_usedQuotCtxts_1799_ = crate::leanh::lean_ctor_get(v___x_1795_, 3);
                v_nextMacroScope_1800_ = crate::leanh::lean_ctor_get(v___x_1795_, 4);
                v_maxRecDepth_1801_ = crate::leanh::lean_ctor_get(v___x_1795_, 5);
                v_ngen_1802_ = crate::leanh::lean_ctor_get(v___x_1795_, 6);
                v_auxDeclNGen_1803_ = crate::leanh::lean_ctor_get(v___x_1795_, 7);
                v_infoState_1804_ = crate::leanh::lean_ctor_get(v___x_1795_, 8);
                v_traceState_1805_ = crate::leanh::lean_ctor_get(v___x_1795_, 9);
                v_snapshotTasks_1806_ = crate::leanh::lean_ctor_get(v___x_1795_, 10);
                v_isSharedCheck_1818_ = (!crate::leanh::lean_is_exclusive(v___x_1795_)) as u8;
                if v_isSharedCheck_1818_ == 0 {
                    v___x_1808_ = v___x_1795_;
                    v_isShared_1809_ = v_isSharedCheck_1818_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_1806_);
                    crate::leanh::lean_inc(v_traceState_1805_);
                    crate::leanh::lean_inc(v_infoState_1804_);
                    crate::leanh::lean_inc(v_auxDeclNGen_1803_);
                    crate::leanh::lean_inc(v_ngen_1802_);
                    crate::leanh::lean_inc(v_maxRecDepth_1801_);
                    crate::leanh::lean_inc(v_nextMacroScope_1800_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_1799_);
                    crate::leanh::lean_inc(v_scopes_1798_);
                    crate::leanh::lean_inc(v_messages_1797_);
                    crate::leanh::lean_inc(v_env_1796_);
                    crate::leanh::lean_dec(v___x_1795_);
                    v___x_1808_ = crate::leanh::lean_box(0);
                    v_isShared_1809_ = v_isSharedCheck_1818_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1810_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1810_, 0, v___y_1793_);
                crate::leanh::lean_ctor_set(v___x_1810_, 1, v___y_1790_);
                crate::leanh::lean_ctor_set(v___x_1810_, 2, v___y_1794_);
                v___x_1811_ = l_Lean_Parser_Term_Doc_addRecommendedSpelling(
                    v_env_1796_,
                    v___x_1810_,
                    v___y_1791_,
                );
                if v_isShared_1809_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1808_, 0, v___x_1811_);
                    v___x_1813_ = v___x_1808_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1817_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_messages_1797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_scopes_1798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_usedQuotCtxts_1799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_nextMacroScope_1800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 5, v_maxRecDepth_1801_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 6, v_ngen_1802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 7, v_auxDeclNGen_1803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 8, v_infoState_1804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 9, v_traceState_1805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 10, v_snapshotTasks_1806_);
                    v___x_1813_ = v_reuseFailAlloc_1817_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1814_ = lean_st_ref_set(v___y_1792_, v___x_1813_);
                v___x_1815_ = crate::leanh::lean_box(0);
                v___x_1816_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1816_, 0, v___x_1815_);
                return v___x_1816_;
            }
            4 => {
                v___x_1825_ = l_Lean_TSyntax_getString(v___y_1824_);
                crate::leanh::lean_dec(v___y_1824_);
                v___x_1826_ = l_Lean_TSyntax_getString(v___y_1823_);
                crate::leanh::lean_dec(v___y_1823_);
                if crate::leanh::lean_obj_tag(v___y_1820_) == 0 {
                    v___x_1827_ = crate::leanh::lean_box(0);
                    v___y_1790_ = v___x_1826_;
                    v___y_1791_ = v___y_1822_;
                    v___y_1792_ = v___y_1821_;
                    v___y_1793_ = v___x_1825_;
                    v___y_1794_ = v___x_1827_;
                    state = 1;
                    continue;
                } else {
                    v_val_1828_ = crate::leanh::lean_ctor_get(v___y_1820_, 0);
                    v_isSharedCheck_1836_ = (!crate::leanh::lean_is_exclusive(v___y_1820_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v___x_1830_ = v___y_1820_;
                        v_isShared_1831_ = v_isSharedCheck_1836_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1828_);
                        crate::leanh::lean_dec(v___y_1820_);
                        v___x_1830_ = crate::leanh::lean_box(0);
                        v_isShared_1831_ = v_isSharedCheck_1836_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___x_1832_ = l_Lean_TSyntax_getDocString(v_val_1828_);
                crate::leanh::lean_dec(v_val_1828_);
                if v_isShared_1831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1830_, 0, v___x_1832_);
                    v___x_1834_ = v___x_1830_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1835_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1832_);
                    v___x_1834_ = v_reuseFailAlloc_1835_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___y_1790_ = v___x_1826_;
                v___y_1791_ = v___y_1822_;
                v___y_1792_ = v___y_1821_;
                v___y_1793_ = v___x_1825_;
                v___y_1794_ = v___x_1834_;
                state = 1;
                continue;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_1843_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_1843_, 1);
                    v___y_1820_ = v___y_1838_;
                    v___y_1821_ = v___y_1840_;
                    v___y_1822_ = v___y_1839_;
                    v___y_1823_ = v___y_1841_;
                    v___y_1824_ = v___y_1842_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_1842_);
                    crate::leanh::lean_dec(v___y_1841_);
                    crate::leanh::lean_dec_ref(v___y_1839_);
                    crate::leanh::lean_dec(v___y_1838_);
                    return v___y_1843_;
                }
            }
            8 => {
                v_sz_1856_ = lean_array_size(v___y_1855_);
                v___x_1857_ = 0usize;
                v___x_1858_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1(v_sz_1856_, v___x_1857_, v___y_1855_);
                if crate::leanh::lean_obj_tag(v___x_1858_) == 0 {
                    crate::leanh::lean_dec(v___y_1854_);
                    crate::leanh::lean_dec(v___y_1852_);
                    crate::leanh::lean_dec(v___y_1850_);
                    v___x_1859_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once
                        ),
                        _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6,
                    );
                    v___x_1860_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(v___x_1859_, v___y_1853_, v___y_1851_);
                    return v___x_1860_;
                } else {
                    v_val_1861_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                    crate::leanh::lean_inc(v_val_1861_);
                    crate::leanh::lean_dec_ref_known(v___x_1858_, 1);
                    v_sz_1862_ = lean_array_size(v_val_1861_);
                    v___x_1863_ = crate::leanh::lean_box_usize(v_sz_1862_);
                    v___x_1864_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed__const__1;
                    v___x_1865_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__3___boxed as *mut core::ffi::c_void, 10, 3);
                    crate::leanh::lean_closure_set(v___x_1865_, 0, v___x_1863_);
                    crate::leanh::lean_closure_set(v___x_1865_, 1, v___x_1864_);
                    crate::leanh::lean_closure_set(v___x_1865_, 2, v_val_1861_);
                    v___x_1866_ = l_Lean_Elab_Command_liftTermElabM___redArg(
                        v___x_1865_,
                        v___y_1853_,
                        v___y_1851_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1866_) == 0 {
                        v_a_1867_ = crate::leanh::lean_ctor_get(v___x_1866_, 0);
                        crate::leanh::lean_inc(v_a_1867_);
                        crate::leanh::lean_dec_ref_known(v___x_1866_, 1);
                        v___x_1868_ = lean_array_get_size(v_a_1867_);
                        v___x_1869_ = lean_nat_dec_lt(v___x_1848_, v___x_1868_);
                        if v___x_1869_ == 0 {
                            v___y_1820_ = v___y_1850_;
                            v___y_1821_ = v___y_1851_;
                            v___y_1822_ = v_a_1867_;
                            v___y_1823_ = v___y_1852_;
                            v___y_1824_ = v___y_1854_;
                            state = 4;
                            continue;
                        } else {
                            v___x_1870_ = crate::leanh::lean_box(0);
                            v___x_1871_ = lean_nat_dec_le(v___x_1868_, v___x_1868_);
                            if v___x_1871_ == 0 {
                                if v___x_1869_ == 0 {
                                    v___y_1820_ = v___y_1850_;
                                    v___y_1821_ = v___y_1851_;
                                    v___y_1822_ = v_a_1867_;
                                    v___y_1823_ = v___y_1852_;
                                    v___y_1824_ = v___y_1854_;
                                    state = 4;
                                    continue;
                                } else {
                                    v___x_1872_ = lean_usize_of_nat(v___x_1868_);
                                    v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__4(v_a_1867_, v___x_1857_, v___x_1872_, v___x_1870_, v___y_1853_, v___y_1851_);
                                    v___y_1838_ = v___y_1850_;
                                    v___y_1839_ = v_a_1867_;
                                    v___y_1840_ = v___y_1851_;
                                    v___y_1841_ = v___y_1852_;
                                    v___y_1842_ = v___y_1854_;
                                    v___y_1843_ = v___x_1873_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                v___x_1874_ = lean_usize_of_nat(v___x_1868_);
                                v___x_1875_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__4(v_a_1867_, v___x_1857_, v___x_1874_, v___x_1870_, v___y_1853_, v___y_1851_);
                                v___y_1838_ = v___y_1850_;
                                v___y_1839_ = v_a_1867_;
                                v___y_1840_ = v___y_1851_;
                                v___y_1841_ = v___y_1852_;
                                v___y_1842_ = v___y_1854_;
                                v___y_1843_ = v___x_1875_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_1854_);
                        crate::leanh::lean_dec(v___y_1852_);
                        crate::leanh::lean_dec(v___y_1850_);
                        v_a_1876_ = crate::leanh::lean_ctor_get(v___x_1866_, 0);
                        v_isSharedCheck_1883_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1866_)) as u8;
                        if v_isSharedCheck_1883_ == 0 {
                            v___x_1878_ = v___x_1866_;
                            v_isShared_1879_ = v_isSharedCheck_1883_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1876_);
                            crate::leanh::lean_dec(v___x_1866_);
                            v___x_1878_ = crate::leanh::lean_box(0);
                            v_isShared_1879_ = v_isSharedCheck_1883_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            9 => {
                if v_isShared_1879_ == 0 {
                    v___x_1881_ = v___x_1878_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1882_, 0, v_a_1876_);
                    v___x_1881_ = v_reuseFailAlloc_1882_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1881_;
            }
            11 => {
                v___x_1888_ = crate::leanh::lean_unsigned_to_nat(2);
                v_spelling_1889_ = l_Lean_Syntax_getArg(v_x_1785_, v___x_1888_);
                v___x_1890_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__8;
                crate::leanh::lean_inc(v_spelling_1889_);
                v___x_1891_ = l_Lean_Syntax_isOfKind(v_spelling_1889_, v___x_1890_);
                if v___x_1891_ == 0 {
                    crate::leanh::lean_dec(v_spelling_1889_);
                    crate::leanh::lean_dec(v_docs_1885_);
                    crate::leanh::lean_dec(v_x_1785_);
                    v___x_1892_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once
                        ),
                        _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6,
                    );
                    v___x_1893_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(v___x_1892_, v___y_1886_, v___y_1887_);
                    return v___x_1893_;
                } else {
                    v___x_1894_ = crate::leanh::lean_unsigned_to_nat(4);
                    v_notation_1895_ = l_Lean_Syntax_getArg(v_x_1785_, v___x_1894_);
                    crate::leanh::lean_inc(v_notation_1895_);
                    v___x_1896_ = l_Lean_Syntax_isOfKind(v_notation_1895_, v___x_1890_);
                    if v___x_1896_ == 0 {
                        crate::leanh::lean_dec(v_notation_1895_);
                        crate::leanh::lean_dec(v_spelling_1889_);
                        crate::leanh::lean_dec(v_docs_1885_);
                        crate::leanh::lean_dec(v_x_1785_);
                        v___x_1897_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6_once
                            ),
                            _init_l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__6,
                        );
                        v___x_1898_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(v___x_1897_, v___y_1886_, v___y_1887_);
                        return v___x_1898_;
                    } else {
                        v___x_1899_ = crate::leanh::lean_unsigned_to_nat(7);
                        v___x_1900_ = l_Lean_Syntax_getArg(v_x_1785_, v___x_1899_);
                        crate::leanh::lean_dec(v_x_1785_);
                        v___x_1901_ = l_Lean_Syntax_getArgs(v___x_1900_);
                        crate::leanh::lean_dec(v___x_1900_);
                        v___x_1902_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__9;
                        v___x_1903_ = lean_array_get_size(v___x_1901_);
                        v___x_1904_ = lean_nat_dec_lt(v___x_1848_, v___x_1903_);
                        if v___x_1904_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1901_);
                            v___y_1850_ = v_docs_1885_;
                            v___y_1851_ = v___y_1887_;
                            v___y_1852_ = v_spelling_1889_;
                            v___y_1853_ = v___y_1886_;
                            v___y_1854_ = v_notation_1895_;
                            v___y_1855_ = v___x_1902_;
                            state = 8;
                            continue;
                        } else {
                            v___x_1905_ = crate::leanh::lean_box((v___x_1896_) as usize);
                            v___x_1906_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1906_, 0, v___x_1905_);
                            crate::leanh::lean_ctor_set(v___x_1906_, 1, v___x_1902_);
                            v___x_1907_ = lean_nat_dec_le(v___x_1903_, v___x_1903_);
                            if v___x_1907_ == 0 {
                                if v___x_1904_ == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1906_, 2);
                                    crate::leanh::lean_dec_ref(v___x_1901_);
                                    v___y_1850_ = v_docs_1885_;
                                    v___y_1851_ = v___y_1887_;
                                    v___y_1852_ = v_spelling_1889_;
                                    v___y_1853_ = v___y_1886_;
                                    v___y_1854_ = v_notation_1895_;
                                    v___y_1855_ = v___x_1902_;
                                    state = 8;
                                    continue;
                                } else {
                                    v___x_1908_ = 0usize;
                                    v___x_1909_ = lean_usize_of_nat(v___x_1903_);
                                    v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__5(v___x_1896_, v___x_1901_, v___x_1908_, v___x_1909_, v___x_1906_);
                                    crate::leanh::lean_dec_ref(v___x_1901_);
                                    v_snd_1911_ = crate::leanh::lean_ctor_get(v___x_1910_, 1);
                                    crate::leanh::lean_inc(v_snd_1911_);
                                    crate::leanh::lean_dec_ref(v___x_1910_);
                                    v___y_1850_ = v_docs_1885_;
                                    v___y_1851_ = v___y_1887_;
                                    v___y_1852_ = v_spelling_1889_;
                                    v___y_1853_ = v___y_1886_;
                                    v___y_1854_ = v_notation_1895_;
                                    v___y_1855_ = v_snd_1911_;
                                    state = 8;
                                    continue;
                                }
                            } else {
                                v___x_1912_ = 0usize;
                                v___x_1913_ = lean_usize_of_nat(v___x_1903_);
                                v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__5(v___x_1896_, v___x_1901_, v___x_1912_, v___x_1913_, v___x_1906_);
                                crate::leanh::lean_dec_ref(v___x_1901_);
                                v_snd_1915_ = crate::leanh::lean_ctor_get(v___x_1914_, 1);
                                crate::leanh::lean_inc(v_snd_1915_);
                                crate::leanh::lean_dec_ref(v___x_1914_);
                                v___y_1850_ = v_docs_1885_;
                                v___y_1851_ = v___y_1887_;
                                v___y_1852_ = v_spelling_1889_;
                                v___y_1853_ = v___y_1886_;
                                v___y_1854_ = v_notation_1895_;
                                v___y_1855_ = v_snd_1915_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed(
    mut v_x_1929_: *mut crate::leanh::LeanObject,
    mut v_a_1930_: *mut crate::leanh::LeanObject,
    mut v_a_1931_: *mut crate::leanh::LeanObject,
    mut v_a_1932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1933_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling(v_x_1929_, v_a_1930_, v_a_1931_);
    crate::leanh::lean_dec(v_a_1931_);
    crate::leanh::lean_dec_ref(v_a_1930_);
    return v_res_1933_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0(
    mut v_msgData_1934_: *mut crate::leanh::LeanObject,
    mut v___y_1935_: *mut crate::leanh::LeanObject,
    mut v___y_1936_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1938_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___redArg(v_msgData_1934_, v___y_1936_);
    return v___x_1938_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0___boxed(
    mut v_msgData_1939_: *mut crate::leanh::LeanObject,
    mut v___y_1940_: *mut crate::leanh::LeanObject,
    mut v___y_1941_: *mut crate::leanh::LeanObject,
    mut v___y_1942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__0(v_msgData_1939_, v___y_1940_, v___y_1941_);
    crate::leanh::lean_dec(v___y_1941_);
    crate::leanh::lean_dec_ref(v___y_1940_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0(
    mut v_00_u03b1_1944_: *mut crate::leanh::LeanObject,
    mut v_msg_1945_: *mut crate::leanh::LeanObject,
    mut v___y_1946_: *mut crate::leanh::LeanObject,
    mut v___y_1947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1949_ =
        l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___redArg(
            v_msg_1945_,
            v___y_1946_,
            v___y_1947_,
        );
    return v___x_1949_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___boxed(
    mut v_00_u03b1_1950_: *mut crate::leanh::LeanObject,
    mut v_msg_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1955_ = l_Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0(
        v_00_u03b1_1950_,
        v_msg_1951_,
        v___y_1952_,
        v___y_1953_,
    );
    crate::leanh::lean_dec(v___y_1953_);
    crate::leanh::lean_dec_ref(v___y_1952_);
    return v_res_1955_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1(
    mut v_msgData_1956_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1957_: *mut crate::leanh::LeanObject,
    mut v___y_1958_: *mut crate::leanh::LeanObject,
    mut v___y_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1961_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___redArg(v_msgData_1956_, v_macroStack_1957_, v___y_1959_);
    return v___x_1961_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1___boxed(
    mut v_msgData_1962_: *mut crate::leanh::LeanObject,
    mut v_macroStack_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1967_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0_spec__1(v_msgData_1962_, v_macroStack_1963_, v___y_1964_, v___y_1965_);
    crate::leanh::lean_dec(v___y_1965_);
    crate::leanh::lean_dec_ref(v___y_1964_);
    return v_res_1967_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6(
    mut v_00_u03b2_1968_: *mut crate::leanh::LeanObject,
    mut v_m_1969_: *mut crate::leanh::LeanObject,
    mut v_a_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___redArg(v_m_1969_, v_a_1970_);
    return v___x_1971_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6___boxed(
    mut v_00_u03b2_1972_: *mut crate::leanh::LeanObject,
    mut v_m_1973_: *mut crate::leanh::LeanObject,
    mut v_a_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1975_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6(v_00_u03b2_1972_, v_m_1973_, v_a_1974_);
    crate::leanh::lean_dec(v_a_1974_);
    crate::leanh::lean_dec_ref(v_m_1973_);
    return v_res_1975_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7(
    mut v_00_u03b2_1976_: *mut crate::leanh::LeanObject,
    mut v_x_1977_: *mut crate::leanh::LeanObject,
    mut v_x_1978_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1979_: u8 = 0;
    v___x_1979_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7___redArg(v_x_1977_, v_x_1978_);
    return v___x_1979_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7___boxed(
    mut v_00_u03b2_1980_: *mut crate::leanh::LeanObject,
    mut v_x_1981_: *mut crate::leanh::LeanObject,
    mut v_x_1982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1983_: u8 = 0;
    let mut v_r_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7(v_00_u03b2_1980_, v_x_1981_, v_x_1982_);
    crate::leanh::lean_dec_ref(v_x_1982_);
    crate::leanh::lean_dec_ref(v_x_1981_);
    v_r_1984_ = crate::leanh::lean_box((v_res_1983_) as usize);
    return v_r_1984_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11(
    mut v_00_u03b2_1985_: *mut crate::leanh::LeanObject,
    mut v_a_1986_: *mut crate::leanh::LeanObject,
    mut v_x_1987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11___redArg(v_a_1986_, v_x_1987_);
    return v___x_1988_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11___boxed(
    mut v_00_u03b2_1989_: *mut crate::leanh::LeanObject,
    mut v_a_1990_: *mut crate::leanh::LeanObject,
    mut v_x_1991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1992_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__6_spec__11(v_00_u03b2_1989_, v_a_1990_, v_x_1991_);
    crate::leanh::lean_dec(v_x_1991_);
    crate::leanh::lean_dec(v_a_1990_);
    return v_res_1992_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11(
    mut v_00_u03b2_1993_: *mut crate::leanh::LeanObject,
    mut v_x_1994_: *mut crate::leanh::LeanObject,
    mut v_x_1995_: usize,
    mut v_x_1996_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1997_: u8 = 0;
    v___x_1997_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___redArg(v_x_1994_, v_x_1995_, v_x_1996_);
    return v___x_1997_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11___boxed(
    mut v_00_u03b2_1998_: *mut crate::leanh::LeanObject,
    mut v_x_1999_: *mut crate::leanh::LeanObject,
    mut v_x_2000_: *mut crate::leanh::LeanObject,
    mut v_x_2001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_9796__boxed_2002_: usize = 0;
    let mut v_res_2003_: u8 = 0;
    let mut v_r_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_9796__boxed_2002_ = crate::leanh::lean_unbox_usize(v_x_2000_);
    crate::leanh::lean_dec(v_x_2000_);
    v_res_2003_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11(v_00_u03b2_1998_, v_x_1999_, v_x_9796__boxed_2002_, v_x_2001_);
    crate::leanh::lean_dec_ref(v_x_2001_);
    crate::leanh::lean_dec_ref(v_x_1999_);
    v_r_2004_ = crate::leanh::lean_box((v_res_2003_) as usize);
    return v_r_2004_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14(
    mut v_00_u03b2_2005_: *mut crate::leanh::LeanObject,
    mut v_keys_2006_: *mut crate::leanh::LeanObject,
    mut v_vals_2007_: *mut crate::leanh::LeanObject,
    mut v_heq_2008_: *mut crate::leanh::LeanObject,
    mut v_i_2009_: *mut crate::leanh::LeanObject,
    mut v_k_2010_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2011_: u8 = 0;
    v___x_2011_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14___redArg(v_keys_2006_, v_i_2009_, v_k_2010_);
    return v___x_2011_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14___boxed(
    mut v_00_u03b2_2012_: *mut crate::leanh::LeanObject,
    mut v_keys_2013_: *mut crate::leanh::LeanObject,
    mut v_vals_2014_: *mut crate::leanh::LeanObject,
    mut v_heq_2015_: *mut crate::leanh::LeanObject,
    mut v_i_2016_: *mut crate::leanh::LeanObject,
    mut v_k_2017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2018_: u8 = 0;
    let mut v_r_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2018_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2_spec__4_spec__7_spec__11_spec__14(v_00_u03b2_2012_, v_keys_2013_, v_vals_2014_, v_heq_2015_, v_i_2016_, v_k_2017_);
    crate::leanh::lean_dec_ref(v_k_2017_);
    crate::leanh::lean_dec_ref(v_vals_2014_);
    crate::leanh::lean_dec_ref(v_keys_2013_);
    v_r_2019_ = crate::leanh::lean_box((v_res_2018_) as usize);
    return v_r_2019_;
}
pub unsafe fn l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2031_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2032_ = l_Lean_Elab_Term_Doc_elabRecommendedSpelling___closed__4;
    v___x_2033_ = l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___closed__4;
    v___x_2034_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2035_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2031_,
        v___x_2032_,
        v___x_2033_,
        v___x_2034_,
    );
    return v___x_2035_;
}
pub unsafe fn l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1___boxed(
    mut v_a_2036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2037_ = l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1();
    return v_res_2037_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(
    mut v_as_2038_: *mut crate::leanh::LeanObject,
    mut v_i_2039_: usize,
    mut v_stop_2040_: usize,
    mut v_b_2041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2042_: u8 = 0;
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: usize = 0;
    let mut v___x_2046_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2042_ = lean_usize_dec_eq(v_i_2039_, v_stop_2040_);
                if v___x_2042_ == 0 {
                    v___x_2043_ = lean_array_uget_borrowed(v_as_2038_, v_i_2039_);
                    v___x_2044_ = l_Array_append___redArg(v_b_2041_, v___x_2043_);
                    v___x_2045_ = 1usize;
                    v___x_2046_ = lean_usize_add(v_i_2039_, v___x_2045_);
                    v_i_2039_ = v___x_2046_;
                    v_b_2041_ = v___x_2044_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2041_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0___boxed(
    mut v_as_2048_: *mut crate::leanh::LeanObject,
    mut v_i_2049_: *mut crate::leanh::LeanObject,
    mut v_stop_2050_: *mut crate::leanh::LeanObject,
    mut v_b_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2052_: usize = 0;
    let mut v_stop_boxed_2053_: usize = 0;
    let mut v_res_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2052_ = crate::leanh::lean_unbox_usize(v_i_2049_);
    crate::leanh::lean_dec(v_i_2049_);
    v_stop_boxed_2053_ = crate::leanh::lean_unbox_usize(v_stop_2050_);
    crate::leanh::lean_dec(v_stop_2050_);
    v_res_2054_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(v_as_2048_, v_i_boxed_2052_, v_stop_boxed_2053_, v_b_2051_);
    crate::leanh::lean_dec_ref(v_as_2048_);
    return v_res_2054_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2055_ = l_Array_instInhabited(crate::leanh::lean_box(0));
    return v___x_2055_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2056_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0,
    );
    v___x_2057_ = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(v___x_2056_);
    return v___x_2057_;
}
pub unsafe fn l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(
    mut v_a_2060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exportEntriesFn_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_importedEntries_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exported_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: u8 = 0;
    v___x_2062_ = lean_st_ref_get(v_a_2060_);
    v___x_2063_ = lean_st_ref_get(v_a_2060_);
    v___x_2064_ = lean_st_ref_get(v_a_2060_);
    v_env_2065_ = crate::leanh::lean_ctor_get(v___x_2062_, 0);
    crate::leanh::lean_inc_ref(v_env_2065_);
    crate::leanh::lean_dec(v___x_2062_);
    v_env_2066_ = crate::leanh::lean_ctor_get(v___x_2063_, 0);
    crate::leanh::lean_inc_ref(v_env_2066_);
    crate::leanh::lean_dec(v___x_2063_);
    v_env_2067_ = crate::leanh::lean_ctor_get(v___x_2064_, 0);
    crate::leanh::lean_inc_ref(v_env_2067_);
    crate::leanh::lean_dec(v___x_2064_);
    v___x_2068_ = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
    v_toEnvExtension_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
    v_exportEntriesFn_2070_ = crate::leanh::lean_ctor_get(v___x_2068_, 4);
    v_asyncMode_2071_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2069_, 2);
    v___x_2072_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__0,
    );
    v___x_2073_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__1,
    );
    v___x_2074_ = crate::leanh::lean_box(0);
    v___x_2075_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(
        v___x_2073_,
        v_toEnvExtension_2069_,
        v_env_2065_,
        v_asyncMode_2071_,
        v___x_2074_,
    );
    v_importedEntries_2076_ = crate::leanh::lean_ctor_get(v___x_2075_, 0);
    crate::leanh::lean_inc_ref(v_importedEntries_2076_);
    crate::leanh::lean_dec(v___x_2075_);
    v___x_2077_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2072_,
        v___x_2068_,
        v_env_2067_,
        v_asyncMode_2071_,
        v___x_2074_,
    );
    crate::leanh::lean_inc_ref(v_exportEntriesFn_2070_);
    v___x_2078_ = crate::leanh::lean_apply_2(v_exportEntriesFn_2070_, v_env_2066_, v___x_2077_);
    v_exported_2079_ = crate::leanh::lean_ctor_get(v___x_2078_, 0);
    crate::leanh::lean_inc(v_exported_2079_);
    crate::leanh::lean_dec_ref(v___x_2078_);
    v___x_2080_ = lean_array_push(v_importedEntries_2076_, v_exported_2079_);
    v___x_2081_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2082_ = l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___closed__2;
    v___x_2083_ = lean_array_get_size(v___x_2080_);
    v___x_2084_ = lean_nat_dec_lt(v___x_2081_, v___x_2083_);
    if v___x_2084_ == 0 {
        let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2080_);
        v___x_2085_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2085_, 0, v___x_2082_);
        return v___x_2085_;
    } else {
        let mut v___x_2086_: u8 = 0;
        v___x_2086_ = lean_nat_dec_le(v___x_2083_, v___x_2083_);
        if v___x_2086_ == 0 {
            if v___x_2084_ == 0 {
                let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_2080_);
                v___x_2087_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2087_, 0, v___x_2082_);
                return v___x_2087_;
            } else {
                let mut v___x_2088_: usize = 0;
                let mut v___x_2089_: usize = 0;
                let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_2088_ = 0usize;
                v___x_2089_ = lean_usize_of_nat(v___x_2083_);
                v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(v___x_2080_, v___x_2088_, v___x_2089_, v___x_2082_);
                crate::leanh::lean_dec_ref(v___x_2080_);
                v___x_2091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2091_, 0, v___x_2090_);
                return v___x_2091_;
            }
        } else {
            let mut v___x_2092_: usize = 0;
            let mut v___x_2093_: usize = 0;
            let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_2092_ = 0usize;
            v___x_2093_ = lean_usize_of_nat(v___x_2083_);
            v___x_2094_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(v___x_2080_, v___x_2092_, v___x_2093_, v___x_2082_);
            crate::leanh::lean_dec_ref(v___x_2080_);
            v___x_2095_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_2095_, 0, v___x_2094_);
            return v___x_2095_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___boxed(
    mut v_a_2096_: *mut crate::leanh::LeanObject,
    mut v_a_2097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2098_ = l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(v_a_2096_);
    crate::leanh::lean_dec(v_a_2096_);
    return v_res_2098_;
}
pub unsafe fn l_Lean_Elab_Term_Doc_allRecommendedSpellings(
    mut v_a_2099_: *mut crate::leanh::LeanObject,
    mut v_a_2100_: *mut crate::leanh::LeanObject,
    mut v_a_2101_: *mut crate::leanh::LeanObject,
    mut v_a_2102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(v_a_2102_);
    return v___x_2104_;
}
pub unsafe fn l_Lean_Elab_Term_Doc_allRecommendedSpellings___boxed(
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2110_ =
        l_Lean_Elab_Term_Doc_allRecommendedSpellings(v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
    crate::leanh::lean_dec(v_a_2108_);
    crate::leanh::lean_dec_ref(v_a_2107_);
    crate::leanh::lean_dec(v_a_2106_);
    crate::leanh::lean_dec_ref(v_a_2105_);
    return v_res_2110_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_RecommendedSpelling(
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
    res = l___private_Lean_Elab_RecommendedSpelling_0__Lean_Elab_Term_Doc_elabRecommendedSpelling___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_RecommendedSpelling(
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
pub unsafe fn initialize_Lean_Elab_RecommendedSpelling(
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
    res = runtime_initialize_Lean_Elab_RecommendedSpelling(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_RecommendedSpelling(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_RecommendedSpelling(builtin);
}
