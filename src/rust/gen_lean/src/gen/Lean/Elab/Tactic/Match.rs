// Lean compiler output
// Module: Lean.Elab.Tactic.Match
// Imports: Lean.Elab.Match Lean.Elab.Tactic.Induction
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_getSepArgs, l_Lean_mkIdentFrom, lean_name_append_index_after,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_isOfKind, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_setKind, l_Lean_addMacroScope,
    l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef, l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::l_Lean_Syntax_setArg;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Match::{
    initialize_Lean_Elab_Match, runtime_initialize_Lean_Elab_Match,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_evalTactic, l_Lean_Elab_Tactic_getMainTag___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Induction::{
    initialize_Lean_Elab_Tactic_Induction, runtime_initialize_Lean_Elab_Tactic_Induction,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_expandMacroImpl_x3f;
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
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::ffi::{lean_array_size, lean_array_uget_borrowed};
use crate::ffi::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_shift_left, lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__3_value) as *mut crate::leanh::LeanObject,9855511589286918680 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 121, 110, 116, 104, 101, 116, 105, 99, 72, 111, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,11921244625177918938 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [63, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 111, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__8_value) as *mut crate::leanh::LeanObject,3984140175429830279 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [114, 104, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10_value) as *mut crate::leanh::LeanObject,969147236311963285 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [99, 97, 115, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14_value) as *mut crate::leanh::LeanObject,3714280620155270360 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [99, 97, 115, 101, 65, 114, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__16_value) as *mut crate::leanh::LeanObject,14546932361418667927 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [98, 105, 110, 100, 101, 114, 73, 100, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__18_value) as *mut crate::leanh::LeanObject,13771926289831477797 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__22_value) as *mut crate::leanh::LeanObject,8504843326314613972 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [116, 97, 99, 116, 105, 99, 83, 101, 113, 49, 73, 110, 100, 101, 110, 116, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__24_value) as *mut crate::leanh::LeanObject,17228437386856258271 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [119, 105, 116, 104, 65, 110, 110, 111, 116, 97, 116, 101, 83, 116, 97, 116, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__26_value) as *mut crate::leanh::LeanObject,10829944387272139803 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [119, 105, 116, 104, 95, 97, 110, 110, 111, 116, 97, 116, 101, 95, 115, 116, 97, 116, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 107, 105, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29_value) as *mut crate::leanh::LeanObject,7630385922513644276 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [109, 97, 116, 99, 104, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value) as *mut crate::leanh::LeanObject,13882684686403831161 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__0_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value) as *mut crate::leanh::LeanObject,11514550152210403337 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 115, 0]};
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__4_value) as *mut crate::leanh::LeanObject,13242179749370575553 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_evalMatch___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [114, 101, 102, 105, 110, 101, 0],
    };
static mut l_Lean_Elab_Tactic_evalMatch___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_evalMatch___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__1_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__0_value)
                as *mut crate::leanh::LeanObject,
            17704266427038597681 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalMatch___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalMatch___closed__2_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            110, 111, 73, 109, 112, 108, 105, 99, 105, 116, 76, 97, 109, 98, 100, 97, 0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalMatch___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Tactic_evalMatch___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__2_value)
                as *mut crate::leanh::LeanObject,
            443989315218990986 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Tactic_evalMatch___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Tactic_evalMatch___closed__4_value: crate::leanh::LeanStringObject<20> =
    crate::leanh::LeanStringObject {
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
            110, 111, 95, 105, 109, 112, 108, 105, 99, 105, 116, 95, 108, 97, 109, 98, 100, 97, 37,
            0,
        ],
    };
static mut l_Lean_Elab_Tactic_evalMatch___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_evalMatch___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,18344149449936419494 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__31_value) as *mut crate::leanh::LeanObject,15889294097160086760 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [101, 118, 97, 108, 77, 97, 116, 99, 104, 0]};
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__1_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__13_value) as *mut crate::leanh::LeanObject,12733524109236233889 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__2_value) as *mut crate::leanh::LeanObject,10989285953064031153 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 58 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 52 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 53 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 13 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__10;
    v___x_1992_ = l_String_toRawSubstring_x27(v___x_1991_);
    return v___x_1992_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2012_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_2012_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(
    mut v___x_2042_: *mut crate::leanh::LeanObject,
    mut v___x_2043_: *mut crate::leanh::LeanObject,
    mut v_alts_2044_: *mut crate::leanh::LeanObject,
    mut v_parentTag_2045_: *mut crate::leanh::LeanObject,
    mut v_as_2046_: *mut crate::leanh::LeanObject,
    mut v_sz_2047_: usize,
    mut v_i_2048_: usize,
    mut v_b_2049_: *mut crate::leanh::LeanObject,
    mut v___y_2050_: *mut crate::leanh::LeanObject,
    mut v___y_2051_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2052_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2058_: u8 = 0;
    let mut v_nextIdx_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newCases_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alt_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: usize = 0;
    let mut v___x_2069_: usize = 0;
    let mut v_reuseFailAlloc_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v_nextIdx_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: u8 = 0;
    let mut v_macroScope_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v_quotContext_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_reuseFailAlloc_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2167_: u8 = 0;
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2052_ = lean_usize_dec_lt(v_i_2048_, v_sz_2047_);
                if v___x_2052_ == 0 {
                    crate::leanh::lean_dec(v_parentTag_2045_);
                    crate::leanh::lean_dec(v___x_2043_);
                    crate::leanh::lean_dec(v___x_2042_);
                    v___x_2053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2053_, 0, v_b_2049_);
                    crate::leanh::lean_ctor_set(v___x_2053_, 1, v___y_2051_);
                    return v___x_2053_;
                } else {
                    v_fst_2054_ = crate::leanh::lean_ctor_get(v_b_2049_, 0);
                    v_snd_2055_ = crate::leanh::lean_ctor_get(v_b_2049_, 1);
                    v_isSharedCheck_2168_ = (!crate::leanh::lean_is_exclusive(v_b_2049_)) as u8;
                    if v_isSharedCheck_2168_ == 0 {
                        v___x_2057_ = v_b_2049_;
                        v_isShared_2058_ = v_isSharedCheck_2168_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2055_);
                        crate::leanh::lean_inc(v_fst_2054_);
                        crate::leanh::lean_dec(v_b_2049_);
                        v___x_2057_ = crate::leanh::lean_box(0);
                        v_isShared_2058_ = v_isSharedCheck_2168_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2072_ = crate::leanh::lean_ctor_get(v_snd_2055_, 0);
                v_snd_2073_ = crate::leanh::lean_ctor_get(v_snd_2055_, 1);
                v_isSharedCheck_2167_ = (!crate::leanh::lean_is_exclusive(v_snd_2055_)) as u8;
                if v_isSharedCheck_2167_ == 0 {
                    v___x_2075_ = v_snd_2055_;
                    v_isShared_2076_ = v_isSharedCheck_2167_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2073_);
                    crate::leanh::lean_inc(v_fst_2072_);
                    crate::leanh::lean_dec(v_snd_2055_);
                    v___x_2075_ = crate::leanh::lean_box(0);
                    v_isShared_2076_ = v_isSharedCheck_2167_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_2064_ = lean_array_push(v_fst_2054_, v_alt_2062_);
                if v_isShared_2058_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2057_, 1, v_newCases_2061_);
                    crate::leanh::lean_ctor_set(v___x_2057_, 0, v_nextIdx_2060_);
                    v___x_2066_ = v___x_2057_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_nextIdx_2060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_newCases_2061_);
                    v___x_2066_ = v_reuseFailAlloc_2071_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2067_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2067_, 0, v___x_2064_);
                crate::leanh::lean_ctor_set(v___x_2067_, 1, v___x_2066_);
                v___x_2068_ = 1usize;
                v___x_2069_ = lean_usize_add(v_i_2048_, v___x_2068_);
                v_i_2048_ = v___x_2069_;
                v_b_2049_ = v___x_2067_;
                v___y_2051_ = v___y_2063_;
                state = 0;
                continue;
            }
            4 => {
                v_nextIdx_2077_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_2078_ = lean_array_uget_borrowed(v_as_2046_, v_i_2048_);
                v___x_2079_ = lean_mk_empty_array_with_capacity(v_nextIdx_2077_);
                crate::leanh::lean_inc(v_a_2078_);
                v___x_2080_ = lean_array_push(v___x_2079_, v_a_2078_);
                v___x_2081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4;
                v___x_2082_ = crate::leanh::lean_box(2);
                v___x_2083_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2083_, 0, v___x_2082_);
                crate::leanh::lean_ctor_set(v___x_2083_, 1, v___x_2081_);
                crate::leanh::lean_ctor_set(v___x_2083_, 2, v___x_2080_);
                crate::leanh::lean_inc(v___x_2042_);
                v___x_2084_ = l_Lean_Syntax_setArg(v___x_2042_, v_nextIdx_2077_, v___x_2083_);
                v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__6;
                crate::leanh::lean_inc(v___x_2043_);
                v___x_2086_ = l_Lean_Syntax_isOfKind(v___x_2043_, v___x_2085_);
                if v___x_2086_ == 0 {
                    v___x_2087_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_2100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__9;
                    crate::leanh::lean_inc(v___x_2043_);
                    v___x_2101_ = l_Lean_Syntax_isOfKind(v___x_2043_, v___x_2100_);
                    if v___x_2101_ == 0 {
                        crate::leanh::lean_del_object(v___x_2075_);
                        v_macroScope_2102_ = crate::leanh::lean_ctor_get(v___y_2051_, 0);
                        v_traceMsgs_2103_ = crate::leanh::lean_ctor_get(v___y_2051_, 1);
                        v_expandedMacroDecls_2104_ = crate::leanh::lean_ctor_get(v___y_2051_, 2);
                        v_isSharedCheck_2161_ =
                            (!crate::leanh::lean_is_exclusive(v___y_2051_)) as u8;
                        if v_isSharedCheck_2161_ == 0 {
                            v___x_2106_ = v___y_2051_;
                            v_isShared_2107_ = v_isSharedCheck_2161_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_expandedMacroDecls_2104_);
                            crate::leanh::lean_inc(v_traceMsgs_2103_);
                            crate::leanh::lean_inc(v_macroScope_2102_);
                            crate::leanh::lean_dec(v___y_2051_);
                            v___x_2106_ = crate::leanh::lean_box(0);
                            v_isShared_2107_ = v_isSharedCheck_2161_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___x_2162_ = lean_array_get_size(v_alts_2044_);
                        v___x_2163_ = lean_nat_dec_lt(v_nextIdx_2077_, v___x_2162_);
                        if v___x_2163_ == 0 {
                            crate::leanh::lean_inc(v_parentTag_2045_);
                            v___y_2089_ = v_parentTag_2045_;
                            state = 5;
                            continue;
                        } else {
                            v___x_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__32;
                            crate::leanh::lean_inc(v_fst_2072_);
                            v___x_2165_ = lean_name_append_index_after(v___x_2164_, v_fst_2072_);
                            crate::leanh::lean_inc(v_parentTag_2045_);
                            v___x_2166_ = l_Lean_Name_append(v_parentTag_2045_, v___x_2165_);
                            v___y_2089_ = v___x_2166_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2075_);
                    v_nextIdx_2060_ = v_fst_2072_;
                    v_newCases_2061_ = v_snd_2073_;
                    v_alt_2062_ = v___x_2084_;
                    v___y_2063_ = v___y_2051_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                v_ref_2090_ = crate::leanh::lean_ctor_get(v___y_2050_, 5);
                v___x_2091_ = l_Lean_mkIdentFrom(v___x_2043_, v___y_2089_, v___x_2086_);
                v___x_2092_ = l_Lean_SourceInfo_fromRef(v_ref_2090_, v___x_2086_);
                v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7;
                crate::leanh::lean_inc(v___x_2092_);
                if v_isShared_2076_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2075_, 2);
                    crate::leanh::lean_ctor_set(v___x_2075_, 1, v___x_2093_);
                    crate::leanh::lean_ctor_set(v___x_2075_, 0, v___x_2092_);
                    v___x_2095_ = v___x_2075_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2099_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2099_, 1, v___x_2093_);
                    v___x_2095_ = v_reuseFailAlloc_2099_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2096_ =
                    l_Lean_Syntax_node2(v___x_2092_, v___x_2085_, v___x_2095_, v___x_2091_);
                v___x_2097_ = lean_nat_add(v_fst_2072_, v_nextIdx_2077_);
                crate::leanh::lean_dec(v_fst_2072_);
                v___x_2098_ = l_Lean_Syntax_setArg(v___x_2084_, v___x_2087_, v___x_2096_);
                v_nextIdx_2060_ = v___x_2097_;
                v_newCases_2061_ = v_snd_2073_;
                v_alt_2062_ = v___x_2098_;
                v___y_2063_ = v___y_2051_;
                state = 2;
                continue;
            }
            7 => {
                v_quotContext_2108_ = crate::leanh::lean_ctor_get(v___y_2050_, 1);
                v_ref_2109_ = crate::leanh::lean_ctor_get(v___y_2050_, 5);
                v___x_2110_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2111_ = lean_nat_add(v_macroScope_2102_, v_nextIdx_2077_);
                if v_isShared_2107_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2106_, 0, v___x_2111_);
                    v___x_2113_ = v___x_2106_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2160_, 1, v_traceMsgs_2103_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2160_,
                        2,
                        v_expandedMacroDecls_2104_,
                    );
                    v___x_2113_ = v_reuseFailAlloc_2160_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2114_ = l_Lean_SourceInfo_fromRef(v_ref_2109_, v___x_2101_);
                v___x_2115_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__7;
                crate::leanh::lean_inc_n(v___x_2114_, 15);
                v___x_2116_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2116_, 0, v___x_2114_);
                crate::leanh::lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                v___x_2117_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__11);
                v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__12;
                crate::leanh::lean_inc(v_quotContext_2108_);
                v___x_2119_ =
                    l_Lean_addMacroScope(v_quotContext_2108_, v___x_2118_, v_macroScope_2102_);
                v___x_2120_ = crate::leanh::lean_box(0);
                v___x_2121_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2121_, 0, v___x_2114_);
                crate::leanh::lean_ctor_set(v___x_2121_, 1, v___x_2117_);
                crate::leanh::lean_ctor_set(v___x_2121_, 2, v___x_2119_);
                crate::leanh::lean_ctor_set(v___x_2121_, 3, v___x_2120_);
                v___x_2122_ =
                    l_Lean_Syntax_node2(v___x_2114_, v___x_2085_, v___x_2116_, v___x_2121_);
                v___x_2123_ = l_Lean_Syntax_getArg(v___x_2122_, v_nextIdx_2077_);
                v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__14;
                v___x_2125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__15;
                v___x_2126_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2126_, 0, v___x_2114_);
                crate::leanh::lean_ctor_set(v___x_2126_, 1, v___x_2124_);
                v___x_2127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__17;
                v___x_2128_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__19;
                v___x_2129_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2128_, v___x_2123_);
                v___x_2130_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__20);
                v___x_2131_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2131_, 0, v___x_2114_);
                crate::leanh::lean_ctor_set(v___x_2131_, 1, v___x_2081_);
                crate::leanh::lean_ctor_set(v___x_2131_, 2, v___x_2130_);
                crate::leanh::lean_inc_ref(v___x_2131_);
                v___x_2132_ =
                    l_Lean_Syntax_node2(v___x_2114_, v___x_2127_, v___x_2129_, v___x_2131_);
                v___x_2133_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2081_, v___x_2132_);
                v___x_2134_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_2135_ = l_Lean_Syntax_getArg(v___x_2084_, v___x_2134_);
                v___x_2136_ = l_Lean_SourceInfo_fromRef(v___x_2135_, v___x_2052_);
                v___x_2137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__21;
                v___x_2138_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2136_);
                crate::leanh::lean_ctor_set(v___x_2138_, 1, v___x_2137_);
                v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__23;
                v___x_2140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__25;
                v___x_2141_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__27;
                v___x_2142_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__28;
                v___x_2143_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2114_);
                crate::leanh::lean_ctor_set(v___x_2143_, 1, v___x_2142_);
                v___x_2144_ = l_Lean_Syntax_getArg(v___x_2084_, v___x_2110_);
                v___x_2145_ = lean_mk_empty_array_with_capacity(v___x_2134_);
                v___x_2146_ = lean_array_push(v___x_2145_, v___x_2144_);
                v___x_2147_ = lean_array_push(v___x_2146_, v___x_2135_);
                v___x_2148_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2148_, 0, v___x_2082_);
                crate::leanh::lean_ctor_set(v___x_2148_, 1, v___x_2081_);
                crate::leanh::lean_ctor_set(v___x_2148_, 2, v___x_2147_);
                v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__29;
                v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__30;
                v___x_2151_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2151_, 0, v___x_2114_);
                crate::leanh::lean_ctor_set(v___x_2151_, 1, v___x_2149_);
                v___x_2152_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2150_, v___x_2151_);
                v___x_2153_ = l_Lean_Syntax_node3(
                    v___x_2114_,
                    v___x_2141_,
                    v___x_2143_,
                    v___x_2148_,
                    v___x_2152_,
                );
                crate::leanh::lean_inc(v___x_2043_);
                v___x_2154_ = l_Lean_Syntax_node3(
                    v___x_2114_,
                    v___x_2081_,
                    v___x_2153_,
                    v___x_2131_,
                    v___x_2043_,
                );
                v___x_2155_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2140_, v___x_2154_);
                v___x_2156_ = l_Lean_Syntax_node1(v___x_2114_, v___x_2139_, v___x_2155_);
                v___x_2157_ = l_Lean_Syntax_node4(
                    v___x_2114_,
                    v___x_2125_,
                    v___x_2126_,
                    v___x_2133_,
                    v___x_2138_,
                    v___x_2156_,
                );
                v___x_2158_ = lean_array_push(v_snd_2073_, v___x_2157_);
                v___x_2159_ = l_Lean_Syntax_setArg(v___x_2084_, v___x_2087_, v___x_2122_);
                v_nextIdx_2060_ = v_fst_2072_;
                v_newCases_2061_ = v___x_2158_;
                v_alt_2062_ = v___x_2159_;
                v___y_2063_ = v___x_2113_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___boxed(
    mut v___x_2169_: *mut crate::leanh::LeanObject,
    mut v___x_2170_: *mut crate::leanh::LeanObject,
    mut v_alts_2171_: *mut crate::leanh::LeanObject,
    mut v_parentTag_2172_: *mut crate::leanh::LeanObject,
    mut v_as_2173_: *mut crate::leanh::LeanObject,
    mut v_sz_2174_: *mut crate::leanh::LeanObject,
    mut v_i_2175_: *mut crate::leanh::LeanObject,
    mut v_b_2176_: *mut crate::leanh::LeanObject,
    mut v___y_2177_: *mut crate::leanh::LeanObject,
    mut v___y_2178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2179_: usize = 0;
    let mut v_i_boxed_2180_: usize = 0;
    let mut v_res_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2179_ = crate::leanh::lean_unbox_usize(v_sz_2174_);
    crate::leanh::lean_dec(v_sz_2174_);
    v_i_boxed_2180_ = crate::leanh::lean_unbox_usize(v_i_2175_);
    crate::leanh::lean_dec(v_i_2175_);
    v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(v___x_2169_, v___x_2170_, v_alts_2171_, v_parentTag_2172_, v_as_2173_, v_sz_boxed_2179_, v_i_boxed_2180_, v_b_2176_, v___y_2177_, v___y_2178_);
    crate::leanh::lean_dec_ref(v___y_2177_);
    crate::leanh::lean_dec_ref(v_as_2173_);
    crate::leanh::lean_dec_ref(v_alts_2171_);
    return v_res_2181_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(
    mut v_alts_2188_: *mut crate::leanh::LeanObject,
    mut v_parentTag_2189_: *mut crate::leanh::LeanObject,
    mut v_as_2190_: *mut crate::leanh::LeanObject,
    mut v_sz_2191_: usize,
    mut v_i_2192_: usize,
    mut v_b_2193_: *mut crate::leanh::LeanObject,
    mut v___y_2194_: *mut crate::leanh::LeanObject,
    mut v___y_2195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2196_: u8 = 0;
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2202_: u8 = 0;
    let mut v_fst_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2207_: u8 = 0;
    let mut v_nextIdx_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2220_: usize = 0;
    let mut v___x_2221_: usize = 0;
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2229_: u8 = 0;
    let mut v_fst_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2234_: u8 = 0;
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: usize = 0;
    let mut v___x_2240_: usize = 0;
    let mut v_reuseFailAlloc_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2244_: u8 = 0;
    let mut v_isSharedCheck_2245_: u8 = 0;
    let mut v_unused_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_isSharedCheck_2250_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2196_ = lean_usize_dec_lt(v_i_2192_, v_sz_2191_);
                if v___x_2196_ == 0 {
                    crate::leanh::lean_dec(v_parentTag_2189_);
                    v___x_2197_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2197_, 0, v_b_2193_);
                    crate::leanh::lean_ctor_set(v___x_2197_, 1, v___y_2195_);
                    return v___x_2197_;
                } else {
                    v_snd_2198_ = crate::leanh::lean_ctor_get(v_b_2193_, 1);
                    v_fst_2199_ = crate::leanh::lean_ctor_get(v_b_2193_, 0);
                    v_isSharedCheck_2250_ = (!crate::leanh::lean_is_exclusive(v_b_2193_)) as u8;
                    if v_isSharedCheck_2250_ == 0 {
                        v___x_2201_ = v_b_2193_;
                        v_isShared_2202_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2198_);
                        crate::leanh::lean_inc(v_fst_2199_);
                        crate::leanh::lean_dec(v_b_2193_);
                        v___x_2201_ = crate::leanh::lean_box(0);
                        v_isShared_2202_ = v_isSharedCheck_2250_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2203_ = crate::leanh::lean_ctor_get(v_snd_2198_, 0);
                v_snd_2204_ = crate::leanh::lean_ctor_get(v_snd_2198_, 1);
                v_isSharedCheck_2249_ = (!crate::leanh::lean_is_exclusive(v_snd_2198_)) as u8;
                if v_isSharedCheck_2249_ == 0 {
                    v___x_2206_ = v_snd_2198_;
                    v_isShared_2207_ = v_isSharedCheck_2249_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2204_);
                    crate::leanh::lean_inc(v_fst_2203_);
                    crate::leanh::lean_dec(v_snd_2198_);
                    v___x_2206_ = crate::leanh::lean_box(0);
                    v_isShared_2207_ = v_isSharedCheck_2249_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_nextIdx_2208_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_2209_ = lean_array_uget_borrowed(v_as_2190_, v_i_2192_);
                v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___closed__1;
                crate::leanh::lean_inc(v_a_2209_);
                v___x_2211_ = l_Lean_Syntax_setKind(v_a_2209_, v___x_2210_);
                v___x_2212_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2213_ = l_Lean_Syntax_getArg(v___x_2211_, v___x_2212_);
                v___x_2214_ = l_Lean_Syntax_getArg(v___x_2211_, v_nextIdx_2208_);
                v___x_2215_ = l_Lean_Syntax_getSepArgs(v___x_2214_);
                crate::leanh::lean_dec(v___x_2214_);
                if v_isShared_2207_ == 0 {
                    v___x_2217_ = v___x_2206_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_fst_2203_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_snd_2204_);
                    v___x_2217_ = v_reuseFailAlloc_2248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2202_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2201_, 1, v___x_2217_);
                    v___x_2219_ = v___x_2201_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v_fst_2199_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 1, v___x_2217_);
                    v___x_2219_ = v_reuseFailAlloc_2247_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_2220_ = lean_array_size(v___x_2215_);
                v___x_2221_ = 0usize;
                crate::leanh::lean_inc(v_parentTag_2189_);
                v___x_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0(v___x_2211_, v___x_2213_, v_alts_2188_, v_parentTag_2189_, v___x_2215_, v_sz_2220_, v___x_2221_, v___x_2219_, v___y_2194_, v___y_2195_);
                crate::leanh::lean_dec_ref(v___x_2215_);
                if crate::leanh::lean_obj_tag(v___x_2222_) == 0 {
                    v_a_2223_ = crate::leanh::lean_ctor_get(v___x_2222_, 0);
                    crate::leanh::lean_inc(v_a_2223_);
                    v_snd_2224_ = crate::leanh::lean_ctor_get(v_a_2223_, 1);
                    crate::leanh::lean_inc(v_snd_2224_);
                    v_a_2225_ = crate::leanh::lean_ctor_get(v___x_2222_, 1);
                    crate::leanh::lean_inc(v_a_2225_);
                    crate::leanh::lean_dec_ref_known(v___x_2222_, 2);
                    v_fst_2226_ = crate::leanh::lean_ctor_get(v_a_2223_, 0);
                    v_isSharedCheck_2245_ = (!crate::leanh::lean_is_exclusive(v_a_2223_)) as u8;
                    if v_isSharedCheck_2245_ == 0 {
                        v_unused_2246_ = crate::leanh::lean_ctor_get(v_a_2223_, 1);
                        crate::leanh::lean_dec(v_unused_2246_);
                        v___x_2228_ = v_a_2223_;
                        v_isShared_2229_ = v_isSharedCheck_2245_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_2226_);
                        crate::leanh::lean_dec(v_a_2223_);
                        v___x_2228_ = crate::leanh::lean_box(0);
                        v_isShared_2229_ = v_isSharedCheck_2245_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_parentTag_2189_);
                    return v___x_2222_;
                }
            }
            5 => {
                v_fst_2230_ = crate::leanh::lean_ctor_get(v_snd_2224_, 0);
                v_snd_2231_ = crate::leanh::lean_ctor_get(v_snd_2224_, 1);
                v_isSharedCheck_2244_ = (!crate::leanh::lean_is_exclusive(v_snd_2224_)) as u8;
                if v_isSharedCheck_2244_ == 0 {
                    v___x_2233_ = v_snd_2224_;
                    v_isShared_2234_ = v_isSharedCheck_2244_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2231_);
                    crate::leanh::lean_inc(v_fst_2230_);
                    crate::leanh::lean_dec(v_snd_2224_);
                    v___x_2233_ = crate::leanh::lean_box(0);
                    v_isShared_2234_ = v_isSharedCheck_2244_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2234_ == 0 {
                    v___x_2236_ = v___x_2233_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2243_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_fst_2230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2243_, 1, v_snd_2231_);
                    v___x_2236_ = v_reuseFailAlloc_2243_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2228_, 1, v___x_2236_);
                    v___x_2238_ = v___x_2228_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_fst_2226_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2242_, 1, v___x_2236_);
                    v___x_2238_ = v_reuseFailAlloc_2242_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2239_ = 1usize;
                v___x_2240_ = lean_usize_add(v_i_2192_, v___x_2239_);
                v_i_2192_ = v___x_2240_;
                v_b_2193_ = v___x_2238_;
                v___y_2195_ = v_a_2225_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1___boxed(
    mut v_alts_2251_: *mut crate::leanh::LeanObject,
    mut v_parentTag_2252_: *mut crate::leanh::LeanObject,
    mut v_as_2253_: *mut crate::leanh::LeanObject,
    mut v_sz_2254_: *mut crate::leanh::LeanObject,
    mut v_i_2255_: *mut crate::leanh::LeanObject,
    mut v_b_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2259_: usize = 0;
    let mut v_i_boxed_2260_: usize = 0;
    let mut v_res_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2259_ = crate::leanh::lean_unbox_usize(v_sz_2254_);
    crate::leanh::lean_dec(v_sz_2254_);
    v_i_boxed_2260_ = crate::leanh::lean_unbox_usize(v_i_2255_);
    crate::leanh::lean_dec(v_i_2255_);
    v_res_2261_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(v_alts_2251_, v_parentTag_2252_, v_as_2253_, v_sz_boxed_2259_, v_i_boxed_2260_, v_b_2256_, v___y_2257_, v___y_2258_);
    crate::leanh::lean_dec_ref(v___y_2257_);
    crate::leanh::lean_dec_ref(v_as_2253_);
    crate::leanh::lean_dec_ref(v_alts_2251_);
    return v_res_2261_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(
    mut v_parentTag_2281_: *mut crate::leanh::LeanObject,
    mut v_matchTac_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_matchAlts_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextIdx_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2292_: usize = 0;
    let mut v___x_2293_: usize = 0;
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2300_: u8 = 0;
    let mut v_fst_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_unused_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2324_: u8 = 0;
    let mut v_unused_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2330_: u8 = 0;
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2285_ = crate::leanh::lean_unsigned_to_nat(5);
                v_matchAlts_2286_ = l_Lean_Syntax_getArg(v_matchTac_2282_, v___x_2285_);
                v___x_2287_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2288_ = l_Lean_Syntax_getArg(v_matchAlts_2286_, v___x_2287_);
                crate::leanh::lean_dec(v_matchAlts_2286_);
                v_alts_2289_ = l_Lean_Syntax_getArgs(v___x_2288_);
                crate::leanh::lean_dec(v___x_2288_);
                v_nextIdx_2290_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2291_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__2;
                v_sz_2292_ = lean_array_size(v_alts_2289_);
                v___x_2293_ = 0usize;
                v___x_2294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__1(v_alts_2289_, v_parentTag_2281_, v_alts_2289_, v_sz_2292_, v___x_2293_, v___x_2291_, v_a_2283_, v_a_2284_);
                crate::leanh::lean_dec_ref(v_alts_2289_);
                if crate::leanh::lean_obj_tag(v___x_2294_) == 0 {
                    v_a_2295_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    crate::leanh::lean_inc(v_a_2295_);
                    v_snd_2296_ = crate::leanh::lean_ctor_get(v_a_2295_, 1);
                    crate::leanh::lean_inc(v_snd_2296_);
                    v_a_2297_ = crate::leanh::lean_ctor_get(v___x_2294_, 1);
                    v_isSharedCheck_2324_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2324_ == 0 {
                        v_unused_2325_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                        crate::leanh::lean_dec(v_unused_2325_);
                        v___x_2299_ = v___x_2294_;
                        v_isShared_2300_ = v_isSharedCheck_2324_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2297_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2299_ = crate::leanh::lean_box(0);
                        v_isShared_2300_ = v_isSharedCheck_2324_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_matchTac_2282_);
                    v_a_2326_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    v_a_2327_ = crate::leanh::lean_ctor_get(v___x_2294_, 1);
                    v_isSharedCheck_2334_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2334_ == 0 {
                        v___x_2329_ = v___x_2294_;
                        v_isShared_2330_ = v_isSharedCheck_2334_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2327_);
                        crate::leanh::lean_inc(v_a_2326_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2329_ = crate::leanh::lean_box(0);
                        v_isShared_2330_ = v_isSharedCheck_2334_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_2301_ = crate::leanh::lean_ctor_get(v_a_2295_, 0);
                crate::leanh::lean_inc(v_fst_2301_);
                crate::leanh::lean_dec(v_a_2295_);
                v_snd_2302_ = crate::leanh::lean_ctor_get(v_snd_2296_, 1);
                v_isSharedCheck_2322_ = (!crate::leanh::lean_is_exclusive(v_snd_2296_)) as u8;
                if v_isSharedCheck_2322_ == 0 {
                    v_unused_2323_ = crate::leanh::lean_ctor_get(v_snd_2296_, 0);
                    crate::leanh::lean_dec(v_unused_2323_);
                    v___x_2304_ = v_snd_2296_;
                    v_isShared_2305_ = v_isSharedCheck_2322_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2302_);
                    crate::leanh::lean_dec(v_snd_2296_);
                    v___x_2304_ = crate::leanh::lean_box(0);
                    v_isShared_2305_ = v_isSharedCheck_2322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2306_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__3;
                v___x_2307_ = l_Lean_Syntax_setKind(v_matchTac_2282_, v___x_2306_);
                v___x_2308_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___closed__5;
                v___x_2309_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4;
                v___x_2310_ = crate::leanh::lean_box(2);
                v___x_2311_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2311_, 0, v___x_2310_);
                crate::leanh::lean_ctor_set(v___x_2311_, 1, v___x_2309_);
                crate::leanh::lean_ctor_set(v___x_2311_, 2, v_fst_2301_);
                v___x_2312_ = lean_mk_empty_array_with_capacity(v_nextIdx_2290_);
                v___x_2313_ = lean_array_push(v___x_2312_, v___x_2311_);
                v___x_2314_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2314_, 0, v___x_2310_);
                crate::leanh::lean_ctor_set(v___x_2314_, 1, v___x_2308_);
                crate::leanh::lean_ctor_set(v___x_2314_, 2, v___x_2313_);
                v___x_2315_ = l_Lean_Syntax_setArg(v___x_2307_, v___x_2285_, v___x_2314_);
                if v_isShared_2305_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2304_, 0, v___x_2315_);
                    v___x_2317_ = v___x_2304_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_snd_2302_);
                    v___x_2317_ = v_reuseFailAlloc_2321_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2300_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2299_, 0, v___x_2317_);
                    v___x_2319_ = v___x_2299_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_a_2297_);
                    v___x_2319_ = v_reuseFailAlloc_2320_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2319_;
            }
            5 => {
                if v_isShared_2330_ == 0 {
                    v___x_2332_ = v___x_2329_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2333_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2326_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_a_2327_);
                    v___x_2332_ = v_reuseFailAlloc_2333_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___boxed(
    mut v_parentTag_2335_: *mut crate::leanh::LeanObject,
    mut v_matchTac_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2339_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm(
        v_parentTag_2335_,
        v_matchTac_2336_,
        v_a_2337_,
        v_a_2338_,
    );
    crate::leanh::lean_dec_ref(v_a_2337_);
    return v_res_2339_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalMatch___lam__0(
    mut v_stx_2340_: *mut crate::leanh::LeanObject,
    mut v___x_2341_: *mut crate::leanh::LeanObject,
    mut v___y_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v___y_2347_: *mut crate::leanh::LeanObject,
    mut v___y_2348_: *mut crate::leanh::LeanObject,
    mut v___y_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_x3f_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mayPostpone_2353_: u8 = 0;
    let mut v_errToSorry_2354_: u8 = 0;
    let mut v_autoBoundImplicitContext_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_autoBoundImplicitForbidden_2356_: *mut crate::leanh::LeanObject =
        core::ptr::null_mut();
    let mut v_sectionVars_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sectionFVars_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_implicitLambda_2359_: u8 = 0;
    let mut v_heedElabAsElim_2360_: u8 = 0;
    let mut v_isNoncomputableSection_2361_: u8 = 0;
    let mut v_isMetaSection_2362_: u8 = 0;
    let mut v_ignoreTCFailures_2363_: u8 = 0;
    let mut v_inPattern_2364_: u8 = 0;
    let mut v_tacSnap_x3f_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_saveRecAppSyntax_2366_: u8 = 0;
    let mut v_holesAsSyntheticOpaque_2367_: u8 = 0;
    let mut v_checkDeprecated_2368_: u8 = 0;
    let mut v_fixedTermElabs_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_declName_x3f_2351_ = crate::leanh::lean_ctor_get(v___y_2344_, 0);
    v_macroStack_2352_ = crate::leanh::lean_ctor_get(v___y_2344_, 1);
    v_mayPostpone_2353_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
    );
    v_errToSorry_2354_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
    );
    v_autoBoundImplicitContext_2355_ = crate::leanh::lean_ctor_get(v___y_2344_, 2);
    v_autoBoundImplicitForbidden_2356_ = crate::leanh::lean_ctor_get(v___y_2344_, 3);
    v_sectionVars_2357_ = crate::leanh::lean_ctor_get(v___y_2344_, 4);
    v_sectionFVars_2358_ = crate::leanh::lean_ctor_get(v___y_2344_, 5);
    v_implicitLambda_2359_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
    );
    v_heedElabAsElim_2360_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
    );
    v_isNoncomputableSection_2361_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
    );
    v_isMetaSection_2362_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
    );
    v_ignoreTCFailures_2363_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
    );
    v_inPattern_2364_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
    );
    v_tacSnap_x3f_2365_ = crate::leanh::lean_ctor_get(v___y_2344_, 6);
    v_saveRecAppSyntax_2366_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
    );
    v_holesAsSyntheticOpaque_2367_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
    );
    v_checkDeprecated_2368_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2344_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
    );
    v_fixedTermElabs_2369_ = crate::leanh::lean_ctor_get(v___y_2344_, 7);
    crate::leanh::lean_inc(v___x_2341_);
    v___x_2370_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2370_, 0, v_stx_2340_);
    crate::leanh::lean_ctor_set(v___x_2370_, 1, v___x_2341_);
    crate::leanh::lean_inc(v_macroStack_2352_);
    v___x_2371_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
    crate::leanh::lean_ctor_set(v___x_2371_, 1, v_macroStack_2352_);
    crate::leanh::lean_inc_ref(v_fixedTermElabs_2369_);
    crate::leanh::lean_inc(v_tacSnap_x3f_2365_);
    crate::leanh::lean_inc(v_sectionFVars_2358_);
    crate::leanh::lean_inc(v_sectionVars_2357_);
    crate::leanh::lean_inc_ref(v_autoBoundImplicitForbidden_2356_);
    crate::leanh::lean_inc(v_autoBoundImplicitContext_2355_);
    crate::leanh::lean_inc(v_declName_x3f_2351_);
    v___x_2372_ = crate::leanh::lean_alloc_ctor(0, 8, (11) as u32);
    crate::leanh::lean_ctor_set(v___x_2372_, 0, v_declName_x3f_2351_);
    crate::leanh::lean_ctor_set(v___x_2372_, 1, v___x_2371_);
    crate::leanh::lean_ctor_set(v___x_2372_, 2, v_autoBoundImplicitContext_2355_);
    crate::leanh::lean_ctor_set(v___x_2372_, 3, v_autoBoundImplicitForbidden_2356_);
    crate::leanh::lean_ctor_set(v___x_2372_, 4, v_sectionVars_2357_);
    crate::leanh::lean_ctor_set(v___x_2372_, 5, v_sectionFVars_2358_);
    crate::leanh::lean_ctor_set(v___x_2372_, 6, v_tacSnap_x3f_2365_);
    crate::leanh::lean_ctor_set(v___x_2372_, 7, v_fixedTermElabs_2369_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
        v_mayPostpone_2353_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 1) as u32,
        v_errToSorry_2354_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
        v_implicitLambda_2359_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 3) as u32,
        v_heedElabAsElim_2360_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 4) as u32,
        v_isNoncomputableSection_2361_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 5) as u32,
        v_isMetaSection_2362_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 6) as u32,
        v_ignoreTCFailures_2363_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 7) as u32,
        v_inPattern_2364_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 8) as u32,
        v_saveRecAppSyntax_2366_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 9) as u32,
        v_holesAsSyntheticOpaque_2367_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2372_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 10) as u32,
        v_checkDeprecated_2368_,
    );
    v___x_2373_ = l_Lean_Elab_Tactic_evalTactic(
        v___x_2341_,
        v___y_2342_,
        v___y_2343_,
        v___x_2372_,
        v___y_2345_,
        v___y_2346_,
        v___y_2347_,
        v___y_2348_,
        v___y_2349_,
    );
    crate::leanh::lean_dec_ref_known(v___x_2372_, 8);
    return v___x_2373_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalMatch___lam__0___boxed(
    mut v_stx_2374_: *mut crate::leanh::LeanObject,
    mut v___x_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
    mut v___y_2379_: *mut crate::leanh::LeanObject,
    mut v___y_2380_: *mut crate::leanh::LeanObject,
    mut v___y_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2385_ = l_Lean_Elab_Tactic_evalMatch___lam__0(
        v_stx_2374_,
        v___x_2375_,
        v___y_2376_,
        v___y_2377_,
        v___y_2378_,
        v___y_2379_,
        v___y_2380_,
        v___y_2381_,
        v___y_2382_,
        v___y_2383_,
    );
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    crate::leanh::lean_dec(v___y_2381_);
    crate::leanh::lean_dec_ref(v___y_2380_);
    crate::leanh::lean_dec(v___y_2379_);
    crate::leanh::lean_dec_ref(v___y_2378_);
    crate::leanh::lean_dec(v___y_2377_);
    crate::leanh::lean_dec_ref(v___y_2376_);
    return v_res_2385_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3(
    mut v_currNamespace_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2389_, 0, v_currNamespace_2386_);
    crate::leanh::lean_ctor_set(v___x_2389_, 1, v___y_2388_);
    return v___x_2389_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3___boxed(
    mut v_currNamespace_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2393_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3(
            v_currNamespace_2390_,
            v___y_2391_,
            v___y_2392_,
        );
    crate::leanh::lean_dec_ref(v___y_2391_);
    return v_res_2393_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(
    mut v_x_2394_: *mut crate::leanh::LeanObject,
    mut v___y_2395_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_2394_) == 0 {
        let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2396_ = crate::leanh::lean_ctor_get(v_x_2394_, 0);
        crate::leanh::lean_inc(v_a_2396_);
        v___x_2397_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2397_, 0, v_a_2396_);
        crate::leanh::lean_ctor_set(v___x_2397_, 1, v___y_2395_);
        return v___x_2397_;
    } else {
        let mut v_a_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2398_ = crate::leanh::lean_ctor_get(v_x_2394_, 0);
        crate::leanh::lean_inc(v_a_2398_);
        v___x_2399_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2399_, 0, v_a_2398_);
        crate::leanh::lean_ctor_set(v___x_2399_, 1, v___y_2395_);
        return v___x_2399_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg___boxed(
    mut v_x_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v_x_2400_, v___y_2401_);
    crate::leanh::lean_dec_ref(v_x_2400_);
    return v_res_2402_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0(
    mut v_env_2403_: *mut crate::leanh::LeanObject,
    mut v_stx_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2412_: u8 = 0;
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2417_: u8 = 0;
    let mut v_unused_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2422_: u8 = 0;
    let mut v_snd_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2428_: u8 = 0;
    let mut v___x_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_a_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2438_: u8 = 0;
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_isSharedCheck_2447_: u8 = 0;
    let mut v_a_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2452_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2456_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2407_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_2403_,
                    v_stx_2404_,
                    v___y_2405_,
                    v___y_2406_,
                );
                if crate::leanh::lean_obj_tag(v___x_2407_) == 0 {
                    v_a_2408_ = crate::leanh::lean_ctor_get(v___x_2407_, 0);
                    crate::leanh::lean_inc(v_a_2408_);
                    if crate::leanh::lean_obj_tag(v_a_2408_) == 0 {
                        v_a_2409_ = crate::leanh::lean_ctor_get(v___x_2407_, 1);
                        v_isSharedCheck_2417_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2407_)) as u8;
                        if v_isSharedCheck_2417_ == 0 {
                            v_unused_2418_ = crate::leanh::lean_ctor_get(v___x_2407_, 0);
                            crate::leanh::lean_dec(v_unused_2418_);
                            v___x_2411_ = v___x_2407_;
                            v_isShared_2412_ = v_isSharedCheck_2417_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2409_);
                            crate::leanh::lean_dec(v___x_2407_);
                            v___x_2411_ = crate::leanh::lean_box(0);
                            v_isShared_2412_ = v_isSharedCheck_2417_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_2419_ = crate::leanh::lean_ctor_get(v_a_2408_, 0);
                        v_isSharedCheck_2447_ = (!crate::leanh::lean_is_exclusive(v_a_2408_)) as u8;
                        if v_isSharedCheck_2447_ == 0 {
                            v___x_2421_ = v_a_2408_;
                            v_isShared_2422_ = v_isSharedCheck_2447_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2419_);
                            crate::leanh::lean_dec(v_a_2408_);
                            v___x_2421_ = crate::leanh::lean_box(0);
                            v_isShared_2422_ = v_isSharedCheck_2447_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2448_ = crate::leanh::lean_ctor_get(v___x_2407_, 0);
                    v_a_2449_ = crate::leanh::lean_ctor_get(v___x_2407_, 1);
                    v_isSharedCheck_2456_ = (!crate::leanh::lean_is_exclusive(v___x_2407_)) as u8;
                    if v_isSharedCheck_2456_ == 0 {
                        v___x_2451_ = v___x_2407_;
                        v_isShared_2452_ = v_isSharedCheck_2456_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2449_);
                        crate::leanh::lean_inc(v_a_2448_);
                        crate::leanh::lean_dec(v___x_2407_);
                        v___x_2451_ = crate::leanh::lean_box(0);
                        v_isShared_2452_ = v_isSharedCheck_2456_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2413_ = crate::leanh::lean_box(0);
                if v_isShared_2412_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2411_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2411_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2416_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2416_, 1, v_a_2409_);
                    v___x_2415_ = v_reuseFailAlloc_2416_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2415_;
            }
            3 => {
                v_snd_2423_ = crate::leanh::lean_ctor_get(v_val_2419_, 1);
                crate::leanh::lean_inc(v_snd_2423_);
                crate::leanh::lean_dec(v_val_2419_);
                if crate::leanh::lean_obj_tag(v_snd_2423_) == 0 {
                    crate::leanh::lean_del_object(v___x_2421_);
                    v_a_2424_ = crate::leanh::lean_ctor_get(v___x_2407_, 1);
                    crate::leanh::lean_inc(v_a_2424_);
                    crate::leanh::lean_dec_ref_known(v___x_2407_, 2);
                    v_a_2425_ = crate::leanh::lean_ctor_get(v_snd_2423_, 0);
                    v_isSharedCheck_2433_ = (!crate::leanh::lean_is_exclusive(v_snd_2423_)) as u8;
                    if v_isSharedCheck_2433_ == 0 {
                        v___x_2427_ = v_snd_2423_;
                        v_isShared_2428_ = v_isSharedCheck_2433_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2425_);
                        crate::leanh::lean_dec(v_snd_2423_);
                        v___x_2427_ = crate::leanh::lean_box(0);
                        v_isShared_2428_ = v_isSharedCheck_2433_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_2434_ = crate::leanh::lean_ctor_get(v___x_2407_, 1);
                    crate::leanh::lean_inc(v_a_2434_);
                    crate::leanh::lean_dec_ref_known(v___x_2407_, 2);
                    v_a_2435_ = crate::leanh::lean_ctor_get(v_snd_2423_, 0);
                    v_isSharedCheck_2446_ = (!crate::leanh::lean_is_exclusive(v_snd_2423_)) as u8;
                    if v_isSharedCheck_2446_ == 0 {
                        v___x_2437_ = v_snd_2423_;
                        v_isShared_2438_ = v_isSharedCheck_2446_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2435_);
                        crate::leanh::lean_dec(v_snd_2423_);
                        v___x_2437_ = crate::leanh::lean_box(0);
                        v_isShared_2438_ = v_isSharedCheck_2446_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2428_ == 0 {
                    v___x_2430_ = v___x_2427_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2425_);
                    v___x_2430_ = v_reuseFailAlloc_2432_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2431_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v___x_2430_, v_a_2424_);
                crate::leanh::lean_dec_ref(v___x_2430_);
                return v___x_2431_;
            }
            6 => {
                if v_isShared_2422_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2421_, 0, v_a_2435_);
                    v___x_2440_ = v___x_2421_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_a_2435_);
                    v___x_2440_ = v_reuseFailAlloc_2445_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2438_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2437_, 0, v___x_2440_);
                    v___x_2442_ = v___x_2437_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2444_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2440_);
                    v___x_2442_ = v_reuseFailAlloc_2444_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2443_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v___x_2442_, v_a_2434_);
                crate::leanh::lean_dec_ref(v___x_2442_);
                return v___x_2443_;
            }
            9 => {
                if v_isShared_2452_ == 0 {
                    v___x_2454_ = v___x_2451_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2455_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2448_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_a_2449_);
                    v___x_2454_ = v_reuseFailAlloc_2455_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0___boxed(
    mut v_env_2457_: *mut crate::leanh::LeanObject,
    mut v_stx_2458_: *mut crate::leanh::LeanObject,
    mut v___y_2459_: *mut crate::leanh::LeanObject,
    mut v___y_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2461_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0(
            v_env_2457_,
            v_stx_2458_,
            v___y_2459_,
            v___y_2460_,
        );
    crate::leanh::lean_dec_ref(v___y_2459_);
    return v_res_2461_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4(
    mut v_env_2462_: *mut crate::leanh::LeanObject,
    mut v_options_2463_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2464_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2465_: *mut crate::leanh::LeanObject,
    mut v_n_2466_: *mut crate::leanh::LeanObject,
    mut v___y_2467_: *mut crate::leanh::LeanObject,
    mut v___y_2468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_2462_,
        v_options_2463_,
        v_currNamespace_2464_,
        v_openDecls_2465_,
        v_n_2466_,
    );
    v___x_2470_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2470_, 0, v___x_2469_);
    crate::leanh::lean_ctor_set(v___x_2470_, 1, v___y_2468_);
    return v___x_2470_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4___boxed(
    mut v_env_2471_: *mut crate::leanh::LeanObject,
    mut v_options_2472_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_2473_: *mut crate::leanh::LeanObject,
    mut v_openDecls_2474_: *mut crate::leanh::LeanObject,
    mut v_n_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2478_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4(
            v_env_2471_,
            v_options_2472_,
            v_currNamespace_2473_,
            v_openDecls_2474_,
            v_n_2475_,
            v___y_2476_,
            v___y_2477_,
        );
    crate::leanh::lean_dec_ref(v___y_2476_);
    crate::leanh::lean_dec_ref(v_options_2472_);
    return v_res_2478_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(
    mut v_msgData_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
    mut v___y_2482_: *mut crate::leanh::LeanObject,
    mut v___y_2483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2485_ = lean_st_ref_get(v___y_2483_);
    v_env_2486_ = crate::leanh::lean_ctor_get(v___x_2485_, 0);
    crate::leanh::lean_inc_ref(v_env_2486_);
    crate::leanh::lean_dec(v___x_2485_);
    v___x_2487_ = lean_st_ref_get(v___y_2481_);
    v_mctx_2488_ = crate::leanh::lean_ctor_get(v___x_2487_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2488_);
    crate::leanh::lean_dec(v___x_2487_);
    v_lctx_2489_ = crate::leanh::lean_ctor_get(v___y_2480_, 2);
    v_options_2490_ = crate::leanh::lean_ctor_get(v___y_2482_, 2);
    crate::leanh::lean_inc_ref(v_options_2490_);
    crate::leanh::lean_inc_ref(v_lctx_2489_);
    v___x_2491_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2491_, 0, v_env_2486_);
    crate::leanh::lean_ctor_set(v___x_2491_, 1, v_mctx_2488_);
    crate::leanh::lean_ctor_set(v___x_2491_, 2, v_lctx_2489_);
    crate::leanh::lean_ctor_set(v___x_2491_, 3, v_options_2490_);
    v___x_2492_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2492_, 0, v___x_2491_);
    crate::leanh::lean_ctor_set(v___x_2492_, 1, v_msgData_2479_);
    v___x_2493_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2493_, 0, v___x_2492_);
    return v___x_2493_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
    mut v___y_2496_: *mut crate::leanh::LeanObject,
    mut v___y_2497_: *mut crate::leanh::LeanObject,
    mut v___y_2498_: *mut crate::leanh::LeanObject,
    mut v___y_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2500_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(v_msgData_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_);
    crate::leanh::lean_dec(v___y_2498_);
    crate::leanh::lean_dec_ref(v___y_2497_);
    crate::leanh::lean_dec(v___y_2496_);
    crate::leanh::lean_dec_ref(v___y_2495_);
    return v_res_2500_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: f64 = 0.0;
    v___x_2501_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2502_ = lean_float_of_nat(v___x_2501_);
    return v___x_2502_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(
    mut v_cls_2506_: *mut crate::leanh::LeanObject,
    mut v_msg_2507_: *mut crate::leanh::LeanObject,
    mut v___y_2508_: *mut crate::leanh::LeanObject,
    mut v___y_2509_: *mut crate::leanh::LeanObject,
    mut v___y_2510_: *mut crate::leanh::LeanObject,
    mut v___y_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2531_: u8 = 0;
    let mut v_tid_2532_: u64 = 0;
    let mut v_traces_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: f64 = 0.0;
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2557_: u8 = 0;
    let mut v_isSharedCheck_2558_: u8 = 0;
    let mut v_isSharedCheck_2559_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2513_ = crate::leanh::lean_ctor_get(v___y_2510_, 5);
                v___x_2514_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(v_msg_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
                v_a_2515_ = crate::leanh::lean_ctor_get(v___x_2514_, 0);
                v_isSharedCheck_2559_ = (!crate::leanh::lean_is_exclusive(v___x_2514_)) as u8;
                if v_isSharedCheck_2559_ == 0 {
                    v___x_2517_ = v___x_2514_;
                    v_isShared_2518_ = v_isSharedCheck_2559_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2515_);
                    crate::leanh::lean_dec(v___x_2514_);
                    v___x_2517_ = crate::leanh::lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2559_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2519_ = lean_st_ref_take(v___y_2511_);
                v_traceState_2520_ = crate::leanh::lean_ctor_get(v___x_2519_, 4);
                v_env_2521_ = crate::leanh::lean_ctor_get(v___x_2519_, 0);
                v_nextMacroScope_2522_ = crate::leanh::lean_ctor_get(v___x_2519_, 1);
                v_ngen_2523_ = crate::leanh::lean_ctor_get(v___x_2519_, 2);
                v_auxDeclNGen_2524_ = crate::leanh::lean_ctor_get(v___x_2519_, 3);
                v_cache_2525_ = crate::leanh::lean_ctor_get(v___x_2519_, 5);
                v_messages_2526_ = crate::leanh::lean_ctor_get(v___x_2519_, 6);
                v_infoState_2527_ = crate::leanh::lean_ctor_get(v___x_2519_, 7);
                v_snapshotTasks_2528_ = crate::leanh::lean_ctor_get(v___x_2519_, 8);
                v_isSharedCheck_2558_ = (!crate::leanh::lean_is_exclusive(v___x_2519_)) as u8;
                if v_isSharedCheck_2558_ == 0 {
                    v___x_2530_ = v___x_2519_;
                    v_isShared_2531_ = v_isSharedCheck_2558_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2528_);
                    crate::leanh::lean_inc(v_infoState_2527_);
                    crate::leanh::lean_inc(v_messages_2526_);
                    crate::leanh::lean_inc(v_cache_2525_);
                    crate::leanh::lean_inc(v_traceState_2520_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2524_);
                    crate::leanh::lean_inc(v_ngen_2523_);
                    crate::leanh::lean_inc(v_nextMacroScope_2522_);
                    crate::leanh::lean_inc(v_env_2521_);
                    crate::leanh::lean_dec(v___x_2519_);
                    v___x_2530_ = crate::leanh::lean_box(0);
                    v_isShared_2531_ = v_isSharedCheck_2558_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_2532_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_2520_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_2533_ = crate::leanh::lean_ctor_get(v_traceState_2520_, 0);
                v_isSharedCheck_2557_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_2520_)) as u8;
                if v_isSharedCheck_2557_ == 0 {
                    v___x_2535_ = v_traceState_2520_;
                    v_isShared_2536_ = v_isSharedCheck_2557_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_2533_);
                    crate::leanh::lean_dec(v_traceState_2520_);
                    v___x_2535_ = crate::leanh::lean_box(0);
                    v_isShared_2536_ = v_isSharedCheck_2557_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2537_ = crate::leanh::lean_box(0);
                v___x_2538_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__0);
                v___x_2539_ = 0;
                v___x_2540_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1;
                v___x_2541_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_2541_, 0, v_cls_2506_);
                crate::leanh::lean_ctor_set(v___x_2541_, 1, v___x_2537_);
                crate::leanh::lean_ctor_set(v___x_2541_, 2, v___x_2540_);
                crate::leanh::lean_ctor_set_float(
                    v___x_2541_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_2538_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_2541_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_2538_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2541_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_2539_,
                );
                v___x_2542_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__2;
                v___x_2543_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2543_, 0, v___x_2541_);
                crate::leanh::lean_ctor_set(v___x_2543_, 1, v_a_2515_);
                crate::leanh::lean_ctor_set(v___x_2543_, 2, v___x_2542_);
                crate::leanh::lean_inc(v_ref_2513_);
                v___x_2544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2544_, 0, v_ref_2513_);
                crate::leanh::lean_ctor_set(v___x_2544_, 1, v___x_2543_);
                v___x_2545_ = l_Lean_PersistentArray_push___redArg(v_traces_2533_, v___x_2544_);
                if v_isShared_2536_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2535_, 0, v___x_2545_);
                    v___x_2547_ = v___x_2535_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2556_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2556_, 0, v___x_2545_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_2556_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_2532_,
                    );
                    v___x_2547_ = v_reuseFailAlloc_2556_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2530_, 4, v___x_2547_);
                    v___x_2549_ = v___x_2530_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2555_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_env_2521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_nextMacroScope_2522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 2, v_ngen_2523_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 3, v_auxDeclNGen_2524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 4, v___x_2547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 5, v_cache_2525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 6, v_messages_2526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 7, v_infoState_2527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2555_, 8, v_snapshotTasks_2528_);
                    v___x_2549_ = v_reuseFailAlloc_2555_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2550_ = lean_st_ref_set(v___y_2511_, v___x_2549_);
                v___x_2551_ = crate::leanh::lean_box(0);
                if v_isShared_2518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2517_, 0, v___x_2551_);
                    v___x_2553_ = v___x_2517_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
                    v___x_2553_ = v_reuseFailAlloc_2554_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2553_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___boxed(
    mut v_cls_2560_: *mut crate::leanh::LeanObject,
    mut v_msg_2561_: *mut crate::leanh::LeanObject,
    mut v___y_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2567_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_cls_2560_, v_msg_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
    crate::leanh::lean_dec(v___y_2565_);
    crate::leanh::lean_dec_ref(v___y_2564_);
    crate::leanh::lean_dec(v___y_2563_);
    crate::leanh::lean_dec_ref(v___y_2562_);
    return v_res_2567_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(
    mut v_as_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
    mut v___y_2573_: *mut crate::leanh::LeanObject,
    mut v___y_2574_: *mut crate::leanh::LeanObject,
    mut v___y_2575_: *mut crate::leanh::LeanObject,
    mut v___y_2576_: *mut crate::leanh::LeanObject,
    mut v___y_2577_: *mut crate::leanh::LeanObject,
    mut v___y_2578_: *mut crate::leanh::LeanObject,
    mut v___y_2579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2584_: u8 = 0;
    let mut v_tail_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_2571_) == 0 {
                    v___x_2581_ = crate::leanh::lean_box(0);
                    v___x_2582_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2582_, 0, v___x_2581_);
                    return v___x_2582_;
                } else {
                    v_options_2583_ = crate::leanh::lean_ctor_get(v___y_2578_, 2);
                    v_hasTrace_2584_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2583_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2584_ == 0 {
                        v_tail_2585_ = crate::leanh::lean_ctor_get(v_as_2571_, 1);
                        crate::leanh::lean_inc(v_tail_2585_);
                        crate::leanh::lean_dec_ref_known(v_as_2571_, 2);
                        v_as_2571_ = v_tail_2585_;
                        state = 0;
                        continue;
                    } else {
                        v_head_2587_ = crate::leanh::lean_ctor_get(v_as_2571_, 0);
                        crate::leanh::lean_inc(v_head_2587_);
                        v_tail_2588_ = crate::leanh::lean_ctor_get(v_as_2571_, 1);
                        crate::leanh::lean_inc(v_tail_2588_);
                        crate::leanh::lean_dec_ref_known(v_as_2571_, 2);
                        v_fst_2589_ = crate::leanh::lean_ctor_get(v_head_2587_, 0);
                        crate::leanh::lean_inc_n(v_fst_2589_, 2);
                        v_snd_2590_ = crate::leanh::lean_ctor_get(v_head_2587_, 1);
                        crate::leanh::lean_inc(v_snd_2590_);
                        crate::leanh::lean_dec(v_head_2587_);
                        v_inheritedTraceOptions_2591_ =
                            crate::leanh::lean_ctor_get(v___y_2578_, 13);
                        v___x_2592_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1;
                        v___x_2593_ = l_Lean_Name_append(v___x_2592_, v_fst_2589_);
                        v___x_2594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2591_,
                            v_options_2583_,
                            v___x_2593_,
                        );
                        crate::leanh::lean_dec(v___x_2593_);
                        if v___x_2594_ == 0 {
                            crate::leanh::lean_dec(v_snd_2590_);
                            crate::leanh::lean_dec(v_fst_2589_);
                            v_as_2571_ = v_tail_2588_;
                            state = 0;
                            continue;
                        } else {
                            v___x_2596_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2596_, 0, v_snd_2590_);
                            v___x_2597_ = l_Lean_MessageData_ofFormat(v___x_2596_);
                            v___x_2598_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_fst_2589_, v___x_2597_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_);
                            if crate::leanh::lean_obj_tag(v___x_2598_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2598_, 1);
                                v_as_2571_ = v_tail_2588_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_2588_);
                                return v___x_2598_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___boxed(
    mut v_as_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
    mut v___y_2603_: *mut crate::leanh::LeanObject,
    mut v___y_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
    mut v___y_2607_: *mut crate::leanh::LeanObject,
    mut v___y_2608_: *mut crate::leanh::LeanObject,
    mut v___y_2609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2610_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(v_as_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
    crate::leanh::lean_dec(v___y_2608_);
    crate::leanh::lean_dec_ref(v___y_2607_);
    crate::leanh::lean_dec(v___y_2606_);
    crate::leanh::lean_dec_ref(v___y_2605_);
    crate::leanh::lean_dec(v___y_2604_);
    crate::leanh::lean_dec_ref(v___y_2603_);
    crate::leanh::lean_dec(v___y_2602_);
    crate::leanh::lean_dec_ref(v___y_2601_);
    return v_res_2610_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1(
    mut v_env_2611_: *mut crate::leanh::LeanObject,
    mut v_declName_2612_: *mut crate::leanh::LeanObject,
    mut v___y_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2615_: u8 = 0;
    let mut v_env_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: u8 = 0;
    let mut v___x_2619_: u8 = 0;
    v___x_2615_ = 0;
    v_env_2616_ = l_Lean_Environment_setExporting(v_env_2611_, v___x_2615_);
    crate::leanh::lean_inc(v_declName_2612_);
    v___x_2617_ = l_Lean_mkPrivateName(v_env_2616_, v_declName_2612_);
    v___x_2618_ = 1;
    crate::leanh::lean_inc_ref(v_env_2616_);
    v___x_2619_ = l_Lean_Environment_contains(v_env_2616_, v___x_2617_, v___x_2618_);
    if v___x_2619_ == 0 {
        let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2621_: u8 = 0;
        let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2620_ = l_Lean_privateToUserName(v_declName_2612_);
        v___x_2621_ = l_Lean_Environment_contains(v_env_2616_, v___x_2620_, v___x_2618_);
        v___x_2622_ = crate::leanh::lean_box((v___x_2621_) as usize);
        v___x_2623_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2622_);
        crate::leanh::lean_ctor_set(v___x_2623_, 1, v___y_2614_);
        return v___x_2623_;
    } else {
        let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_2616_);
        crate::leanh::lean_dec(v_declName_2612_);
        v___x_2624_ = crate::leanh::lean_box((v___x_2619_) as usize);
        v___x_2625_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2625_, 0, v___x_2624_);
        crate::leanh::lean_ctor_set(v___x_2625_, 1, v___y_2614_);
        return v___x_2625_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1___boxed(
    mut v_env_2626_: *mut crate::leanh::LeanObject,
    mut v_declName_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2630_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1(
            v_env_2626_,
            v_declName_2627_,
            v___y_2628_,
            v___y_2629_,
        );
    crate::leanh::lean_dec_ref(v___y_2628_);
    return v_res_2630_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(
    mut v_a_2631_: *mut crate::leanh::LeanObject,
    mut v_x_2632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2632_) == 0 {
                    v___x_2633_ = crate::leanh::lean_box(0);
                    return v___x_2633_;
                } else {
                    v_key_2634_ = crate::leanh::lean_ctor_get(v_x_2632_, 0);
                    v_value_2635_ = crate::leanh::lean_ctor_get(v_x_2632_, 1);
                    v_tail_2636_ = crate::leanh::lean_ctor_get(v_x_2632_, 2);
                    v___x_2637_ = lean_name_eq(v_key_2634_, v_a_2631_);
                    if v___x_2637_ == 0 {
                        v_x_2632_ = v_tail_2636_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2635_);
                        v___x_2639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2639_, 0, v_value_2635_);
                        return v___x_2639_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg___boxed(
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_x_2641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2642_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(v_a_2640_, v_x_2641_);
    crate::leanh::lean_dec(v_x_2641_);
    crate::leanh::lean_dec(v_a_2640_);
    return v_res_2642_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: u64 = 0;
    v___x_2643_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_2644_ = lean_uint64_of_nat(v___x_2643_);
    return v___x_2644_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(
    mut v_m_2645_: *mut crate::leanh::LeanObject,
    mut v_a_2646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2650_: u64 = 0;
    let mut v___x_2651_: u64 = 0;
    let mut v___x_2652_: u64 = 0;
    let mut v_fold_2653_: u64 = 0;
    let mut v___x_2654_: u64 = 0;
    let mut v___x_2655_: u64 = 0;
    let mut v___x_2656_: u64 = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: usize = 0;
    let mut v___x_2660_: usize = 0;
    let mut v___x_2661_: usize = 0;
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u64 = 0;
    let mut v_hash_2665_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_2647_ = crate::leanh::lean_ctor_get(v_m_2645_, 1);
                v___x_2648_ = lean_array_get_size(v_buckets_2647_);
                if crate::leanh::lean_obj_tag(v_a_2646_) == 0 {
                    v___x_2664_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___closed__0);
                    v___y_2650_ = v___x_2664_;
                    state = 1;
                    continue;
                } else {
                    v_hash_2665_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_2646_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_2650_ = v_hash_2665_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2651_ = 32u64;
                v___x_2652_ = lean_uint64_shift_right(v___y_2650_, v___x_2651_);
                v_fold_2653_ = lean_uint64_xor(v___y_2650_, v___x_2652_);
                v___x_2654_ = 16u64;
                v___x_2655_ = lean_uint64_shift_right(v_fold_2653_, v___x_2654_);
                v___x_2656_ = lean_uint64_xor(v_fold_2653_, v___x_2655_);
                v___x_2657_ = lean_uint64_to_usize(v___x_2656_);
                v___x_2658_ = lean_usize_of_nat(v___x_2648_);
                v___x_2659_ = 1usize;
                v___x_2660_ = lean_usize_sub(v___x_2658_, v___x_2659_);
                v___x_2661_ = lean_usize_land(v___x_2657_, v___x_2660_);
                v___x_2662_ = lean_array_uget_borrowed(v_buckets_2647_, v___x_2661_);
                v___x_2663_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(v_a_2646_, v___x_2662_);
                return v___x_2663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_m_2666_: *mut crate::leanh::LeanObject,
    mut v_a_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(v_m_2666_, v_a_2667_);
    crate::leanh::lean_dec(v_a_2667_);
    crate::leanh::lean_dec_ref(v_m_2666_);
    return v_res_2668_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(
    mut v_keys_2669_: *mut crate::leanh::LeanObject,
    mut v_i_2670_: *mut crate::leanh::LeanObject,
    mut v_k_2671_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: u8 = 0;
    let mut v_k_x27_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: u8 = 0;
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2672_ = lean_array_get_size(v_keys_2669_);
                v___x_2673_ = lean_nat_dec_lt(v_i_2670_, v___x_2672_);
                if v___x_2673_ == 0 {
                    crate::leanh::lean_dec(v_i_2670_);
                    return v___x_2673_;
                } else {
                    v_k_x27_2674_ = lean_array_fget_borrowed(v_keys_2669_, v_i_2670_);
                    v___x_2675_ = l_Lean_instBEqExtraModUse_beq(v_k_2671_, v_k_x27_2674_);
                    if v___x_2675_ == 0 {
                        v___x_2676_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2677_ = lean_nat_add(v_i_2670_, v___x_2676_);
                        crate::leanh::lean_dec(v_i_2670_);
                        v_i_2670_ = v___x_2677_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_2670_);
                        return v___x_2675_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg___boxed(
    mut v_keys_2679_: *mut crate::leanh::LeanObject,
    mut v_i_2680_: *mut crate::leanh::LeanObject,
    mut v_k_2681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2682_: u8 = 0;
    let mut v_r_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2682_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(v_keys_2679_, v_i_2680_, v_k_2681_);
    crate::leanh::lean_dec_ref(v_k_2681_);
    crate::leanh::lean_dec_ref(v_keys_2679_);
    v_r_2683_ = crate::leanh::lean_box((v_res_2682_) as usize);
    return v_r_2683_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__0()
-> usize {
    let mut v___x_2684_: usize = 0;
    let mut v___x_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    v___x_2684_ = 5usize;
    v___x_2685_ = 1usize;
    v___x_2686_ = lean_usize_shift_left(v___x_2685_, v___x_2684_);
    return v___x_2686_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__1()
-> usize {
    let mut v___x_2687_: usize = 0;
    let mut v___x_2688_: usize = 0;
    let mut v___x_2689_: usize = 0;
    v___x_2687_ = 1usize;
    v___x_2688_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__0);
    v___x_2689_ = lean_usize_sub(v___x_2688_, v___x_2687_);
    return v___x_2689_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(
    mut v_x_2690_: *mut crate::leanh::LeanObject,
    mut v_x_2691_: usize,
    mut v_x_2692_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: usize = 0;
    let mut v___x_2696_: usize = 0;
    let mut v___x_2697_: usize = 0;
    let mut v_j_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: u8 = 0;
    let mut v_node_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: usize = 0;
    let mut v___x_2705_: u8 = 0;
    let mut v_ks_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2690_) == 0 {
                    v_es_2693_ = crate::leanh::lean_ctor_get(v_x_2690_, 0);
                    v___x_2694_ = crate::leanh::lean_box(2);
                    v___x_2695_ = 5usize;
                    v___x_2696_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___closed__1);
                    v___x_2697_ = lean_usize_land(v_x_2691_, v___x_2696_);
                    v_j_2698_ = lean_usize_to_nat(v___x_2697_);
                    v___x_2699_ = lean_array_get_borrowed(v___x_2694_, v_es_2693_, v_j_2698_);
                    crate::leanh::lean_dec(v_j_2698_);
                    match crate::leanh::lean_obj_tag(v___x_2699_) {
                        0 => {
                            v_key_2700_ = crate::leanh::lean_ctor_get(v___x_2699_, 0);
                            v___x_2701_ = l_Lean_instBEqExtraModUse_beq(v_x_2692_, v_key_2700_);
                            return v___x_2701_;
                        }
                        1 => {
                            v_node_2702_ = crate::leanh::lean_ctor_get(v___x_2699_, 0);
                            v___x_2703_ = lean_usize_shift_right(v_x_2691_, v___x_2695_);
                            v_x_2690_ = v_node_2702_;
                            v_x_2691_ = v___x_2703_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2705_ = 0;
                            return v___x_2705_;
                        }
                    }
                } else {
                    v_ks_2706_ = crate::leanh::lean_ctor_get(v_x_2690_, 0);
                    v___x_2707_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2708_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(v_ks_2706_, v___x_2707_, v_x_2692_);
                    return v___x_2708_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg___boxed(
    mut v_x_2709_: *mut crate::leanh::LeanObject,
    mut v_x_2710_: *mut crate::leanh::LeanObject,
    mut v_x_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_24783__boxed_2712_: usize = 0;
    let mut v_res_2713_: u8 = 0;
    let mut v_r_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_24783__boxed_2712_ = crate::leanh::lean_unbox_usize(v_x_2710_);
    crate::leanh::lean_dec(v_x_2710_);
    v_res_2713_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(v_x_2709_, v_x_24783__boxed_2712_, v_x_2711_);
    crate::leanh::lean_dec_ref(v_x_2711_);
    crate::leanh::lean_dec_ref(v_x_2709_);
    v_r_2714_ = crate::leanh::lean_box((v_res_2713_) as usize);
    return v_r_2714_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(
    mut v_x_2715_: *mut crate::leanh::LeanObject,
    mut v_x_2716_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2717_: u64 = 0;
    let mut v___x_2718_: usize = 0;
    let mut v___x_2719_: u8 = 0;
    v___x_2717_ = l_Lean_instHashableExtraModUse_hash(v_x_2716_);
    v___x_2718_ = lean_uint64_to_usize(v___x_2717_);
    v___x_2719_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(v_x_2715_, v___x_2718_, v_x_2716_);
    return v___x_2719_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_x_2720_: *mut crate::leanh::LeanObject,
    mut v_x_2721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2722_: u8 = 0;
    let mut v_r_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(v_x_2720_, v_x_2721_);
    crate::leanh::lean_dec_ref(v_x_2721_);
    crate::leanh::lean_dec_ref(v_x_2720_);
    v_r_2723_ = crate::leanh::lean_box((v_res_2722_) as usize);
    return v_r_2723_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2726_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__1;
    v___x_2727_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__0;
    v___x_2728_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2727_,
        v___x_2726_,
    );
    return v___x_2728_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2729_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2729_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2730_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__3);
    v___x_2731_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2731_, 0, v___x_2730_);
    return v___x_2731_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2732_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4);
    v___x_2733_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2733_, 0, v___x_2732_);
    crate::leanh::lean_ctor_set(v___x_2733_, 1, v___x_2732_);
    return v___x_2733_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2734_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__4);
    v___x_2735_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2735_, 0, v___x_2734_);
    crate::leanh::lean_ctor_set(v___x_2735_, 1, v___x_2734_);
    crate::leanh::lean_ctor_set(v___x_2735_, 2, v___x_2734_);
    crate::leanh::lean_ctor_set(v___x_2735_, 3, v___x_2734_);
    crate::leanh::lean_ctor_set(v___x_2735_, 4, v___x_2734_);
    crate::leanh::lean_ctor_set(v___x_2735_, 5, v___x_2734_);
    return v___x_2735_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2740_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__9;
    v___x_2741_ = l_Lean_stringToMessageData(v___x_2740_);
    return v___x_2741_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2743_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__11;
    v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
    return v___x_2744_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg___closed__1;
    v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
    return v___x_2746_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_2747_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8;
    v___x_2748_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4___closed__1;
    v___x_2749_ = l_Lean_Name_append(v___x_2748_, v_cls_2747_);
    return v___x_2749_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__15;
    v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
    return v___x_2752_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2754_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__17;
    v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
    return v___x_2755_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(
    mut v_mod_2760_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2761_: u8,
    mut v_hint_2762_: *mut crate::leanh::LeanObject,
    mut v___y_2763_: *mut crate::leanh::LeanObject,
    mut v___y_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
    mut v___y_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
    mut v___y_2770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_2774_: u8 = 0;
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2797_: u8 = 0;
    let mut v_asyncMode_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2819_: u8 = 0;
    let mut v_unused_2820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2822_: u8 = 0;
    let mut v_unused_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v_options_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_2827_: u8 = 0;
    let mut v_inheritedTraceOptions_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: u8 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: u8 = 0;
    let mut v___x_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2772_ = lean_st_ref_get(v___y_2770_);
                v_env_2773_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                crate::leanh::lean_inc_ref(v_env_2773_);
                crate::leanh::lean_dec(v___x_2772_);
                v_isExporting_2774_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_2773_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_2773_);
                v___x_2775_ = lean_st_ref_get(v___y_2770_);
                v_env_2776_ = crate::leanh::lean_ctor_get(v___x_2775_, 0);
                crate::leanh::lean_inc_ref(v_env_2776_);
                crate::leanh::lean_dec(v___x_2775_);
                v___x_2777_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__2);
                crate::leanh::lean_inc(v_mod_2760_);
                v_entry_2778_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_2778_, 0, v_mod_2760_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_2778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_2774_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_2778_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_2761_,
                );
                v___x_2779_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_2780_ = crate::leanh::lean_box(1);
                v___x_2781_ = crate::leanh::lean_box(0);
                v___x_2824_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_2777_,
                    v___x_2779_,
                    v_env_2776_,
                    v___x_2780_,
                    v___x_2781_,
                );
                v___x_2825_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(v___x_2824_, v_entry_2778_);
                crate::leanh::lean_dec(v___x_2824_);
                if v___x_2825_ == 0 {
                    v_options_2826_ = crate::leanh::lean_ctor_get(v___y_2769_, 2);
                    v_hasTrace_2827_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_2826_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_2827_ == 0 {
                        crate::leanh::lean_dec(v_hint_2762_);
                        crate::leanh::lean_dec(v_mod_2760_);
                        v___y_2783_ = v___y_2768_;
                        v___y_2784_ = v___y_2770_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_2828_ =
                            crate::leanh::lean_ctor_get(v___y_2769_, 13);
                        v_cls_2829_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__8;
                        v___x_2849_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__14);
                        v___x_2850_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_2828_,
                            v_options_2826_,
                            v___x_2849_,
                        );
                        if v___x_2850_ == 0 {
                            crate::leanh::lean_dec(v_hint_2762_);
                            crate::leanh::lean_dec(v_mod_2760_);
                            v___y_2783_ = v___y_2768_;
                            v___y_2784_ = v___y_2770_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2851_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__16);
                            if v_isExporting_2774_ == 0 {
                                v___x_2860_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__21;
                                v___y_2853_ = v___x_2860_;
                                state = 8;
                                continue;
                            } else {
                                v___x_2861_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__22;
                                v___y_2853_ = v___x_2861_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_2778_, 1);
                    crate::leanh::lean_dec(v_hint_2762_);
                    crate::leanh::lean_dec(v_mod_2760_);
                    v___x_2862_ = crate::leanh::lean_box(0);
                    v___x_2863_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2863_, 0, v___x_2862_);
                    return v___x_2863_;
                }
            }
            1 => {
                v___x_2785_ = lean_st_ref_take(v___y_2784_);
                v_toEnvExtension_2786_ = crate::leanh::lean_ctor_get(v___x_2779_, 0);
                v_env_2787_ = crate::leanh::lean_ctor_get(v___x_2785_, 0);
                v_nextMacroScope_2788_ = crate::leanh::lean_ctor_get(v___x_2785_, 1);
                v_ngen_2789_ = crate::leanh::lean_ctor_get(v___x_2785_, 2);
                v_auxDeclNGen_2790_ = crate::leanh::lean_ctor_get(v___x_2785_, 3);
                v_traceState_2791_ = crate::leanh::lean_ctor_get(v___x_2785_, 4);
                v_messages_2792_ = crate::leanh::lean_ctor_get(v___x_2785_, 6);
                v_infoState_2793_ = crate::leanh::lean_ctor_get(v___x_2785_, 7);
                v_snapshotTasks_2794_ = crate::leanh::lean_ctor_get(v___x_2785_, 8);
                v_isSharedCheck_2822_ = (!crate::leanh::lean_is_exclusive(v___x_2785_)) as u8;
                if v_isSharedCheck_2822_ == 0 {
                    v_unused_2823_ = crate::leanh::lean_ctor_get(v___x_2785_, 5);
                    crate::leanh::lean_dec(v_unused_2823_);
                    v___x_2796_ = v___x_2785_;
                    v_isShared_2797_ = v_isSharedCheck_2822_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2794_);
                    crate::leanh::lean_inc(v_infoState_2793_);
                    crate::leanh::lean_inc(v_messages_2792_);
                    crate::leanh::lean_inc(v_traceState_2791_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2790_);
                    crate::leanh::lean_inc(v_ngen_2789_);
                    crate::leanh::lean_inc(v_nextMacroScope_2788_);
                    crate::leanh::lean_inc(v_env_2787_);
                    crate::leanh::lean_dec(v___x_2785_);
                    v___x_2796_ = crate::leanh::lean_box(0);
                    v_isShared_2797_ = v_isSharedCheck_2822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_2798_ = crate::leanh::lean_ctor_get(v_toEnvExtension_2786_, 2);
                v___x_2799_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2779_,
                    v_env_2787_,
                    v_entry_2778_,
                    v_asyncMode_2798_,
                    v___x_2781_,
                );
                v___x_2800_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__5);
                if v_isShared_2797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2796_, 5, v___x_2800_);
                    crate::leanh::lean_ctor_set(v___x_2796_, 0, v___x_2799_);
                    v___x_2802_ = v___x_2796_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2821_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v___x_2799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_nextMacroScope_2788_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 2, v_ngen_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 3, v_auxDeclNGen_2790_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 4, v_traceState_2791_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 5, v___x_2800_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 6, v_messages_2792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 7, v_infoState_2793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 8, v_snapshotTasks_2794_);
                    v___x_2802_ = v_reuseFailAlloc_2821_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2803_ = lean_st_ref_set(v___y_2784_, v___x_2802_);
                v___x_2804_ = lean_st_ref_take(v___y_2783_);
                v_mctx_2805_ = crate::leanh::lean_ctor_get(v___x_2804_, 0);
                v_zetaDeltaFVarIds_2806_ = crate::leanh::lean_ctor_get(v___x_2804_, 2);
                v_postponed_2807_ = crate::leanh::lean_ctor_get(v___x_2804_, 3);
                v_diag_2808_ = crate::leanh::lean_ctor_get(v___x_2804_, 4);
                v_isSharedCheck_2819_ = (!crate::leanh::lean_is_exclusive(v___x_2804_)) as u8;
                if v_isSharedCheck_2819_ == 0 {
                    v_unused_2820_ = crate::leanh::lean_ctor_get(v___x_2804_, 1);
                    crate::leanh::lean_dec(v_unused_2820_);
                    v___x_2810_ = v___x_2804_;
                    v_isShared_2811_ = v_isSharedCheck_2819_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2808_);
                    crate::leanh::lean_inc(v_postponed_2807_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2806_);
                    crate::leanh::lean_inc(v_mctx_2805_);
                    crate::leanh::lean_dec(v___x_2804_);
                    v___x_2810_ = crate::leanh::lean_box(0);
                    v_isShared_2811_ = v_isSharedCheck_2819_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2812_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__6);
                if v_isShared_2811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2810_, 1, v___x_2812_);
                    v___x_2814_ = v___x_2810_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2818_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_mctx_2805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2812_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2818_,
                        2,
                        v_zetaDeltaFVarIds_2806_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 3, v_postponed_2807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2818_, 4, v_diag_2808_);
                    v___x_2814_ = v_reuseFailAlloc_2818_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2815_ = lean_st_ref_set(v___y_2783_, v___x_2814_);
                v___x_2816_ = crate::leanh::lean_box(0);
                v___x_2817_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2817_, 0, v___x_2816_);
                return v___x_2817_;
            }
            6 => {
                v___x_2833_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2833_, 0, v___y_2831_);
                crate::leanh::lean_ctor_set(v___x_2833_, 1, v___y_2832_);
                v___x_2834_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_cls_2829_, v___x_2833_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_);
                if crate::leanh::lean_obj_tag(v___x_2834_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2834_, 1);
                    v___y_2783_ = v___y_2768_;
                    v___y_2784_ = v___y_2770_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_2778_, 1);
                    return v___x_2834_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_2837_);
                v___x_2838_ = l_Lean_stringToMessageData(v___y_2837_);
                v___x_2839_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2839_, 0, v___y_2836_);
                crate::leanh::lean_ctor_set(v___x_2839_, 1, v___x_2838_);
                v___x_2840_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__10);
                v___x_2841_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2841_, 0, v___x_2839_);
                crate::leanh::lean_ctor_set(v___x_2841_, 1, v___x_2840_);
                v___x_2842_ = l_Lean_MessageData_ofName(v_mod_2760_);
                v___x_2843_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2843_, 0, v___x_2841_);
                crate::leanh::lean_ctor_set(v___x_2843_, 1, v___x_2842_);
                v___x_2844_ = l_Lean_Name_isAnonymous(v_hint_2762_);
                if v___x_2844_ == 0 {
                    v___x_2845_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__12);
                    v___x_2846_ = l_Lean_MessageData_ofName(v_hint_2762_);
                    v___x_2847_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2847_, 0, v___x_2845_);
                    crate::leanh::lean_ctor_set(v___x_2847_, 1, v___x_2846_);
                    v___y_2831_ = v___x_2843_;
                    v___y_2832_ = v___x_2847_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_2762_);
                    v___x_2848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__13);
                    v___y_2831_ = v___x_2843_;
                    v___y_2832_ = v___x_2848_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_2853_);
                v___x_2854_ = l_Lean_stringToMessageData(v___y_2853_);
                v___x_2855_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2855_, 0, v___x_2851_);
                crate::leanh::lean_ctor_set(v___x_2855_, 1, v___x_2854_);
                v___x_2856_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__18);
                v___x_2857_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2857_, 0, v___x_2855_);
                crate::leanh::lean_ctor_set(v___x_2857_, 1, v___x_2856_);
                if v_isMeta_2761_ == 0 {
                    v___x_2858_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__19;
                    v___y_2836_ = v___x_2857_;
                    v___y_2837_ = v___x_2858_;
                    state = 7;
                    continue;
                } else {
                    v___x_2859_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___closed__20;
                    v___y_2836_ = v___x_2857_;
                    v___y_2837_ = v___x_2859_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4___boxed(
    mut v_mod_2864_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2865_: *mut crate::leanh::LeanObject,
    mut v_hint_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
    mut v___y_2868_: *mut crate::leanh::LeanObject,
    mut v___y_2869_: *mut crate::leanh::LeanObject,
    mut v___y_2870_: *mut crate::leanh::LeanObject,
    mut v___y_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_2876_: u8 = 0;
    let mut v_res_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2876_ = (crate::leanh::lean_unbox(v_isMeta_2865_) as u8);
    v_res_2877_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(v_mod_2864_, v_isMeta_boxed_2876_, v_hint_2866_, v___y_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_);
    crate::leanh::lean_dec(v___y_2874_);
    crate::leanh::lean_dec_ref(v___y_2873_);
    crate::leanh::lean_dec(v___y_2872_);
    crate::leanh::lean_dec_ref(v___y_2871_);
    crate::leanh::lean_dec(v___y_2870_);
    crate::leanh::lean_dec_ref(v___y_2869_);
    crate::leanh::lean_dec(v___y_2868_);
    crate::leanh::lean_dec_ref(v___y_2867_);
    return v_res_2877_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(
    mut v___x_2878_: *mut crate::leanh::LeanObject,
    mut v_declName_2879_: *mut crate::leanh::LeanObject,
    mut v_as_2880_: *mut crate::leanh::LeanObject,
    mut v_sz_2881_: usize,
    mut v_i_2882_: usize,
    mut v_b_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
    mut v___y_2888_: *mut crate::leanh::LeanObject,
    mut v___y_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2893_: u8 = 0;
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: usize = 0;
    let mut v___x_2906_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2893_ = lean_usize_dec_lt(v_i_2882_, v_sz_2881_);
                if v___x_2893_ == 0 {
                    crate::leanh::lean_dec(v_declName_2879_);
                    v___x_2894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2894_, 0, v_b_2883_);
                    return v___x_2894_;
                } else {
                    v___x_2895_ = l_Lean_Environment_header(v___x_2878_);
                    v_modules_2896_ = crate::leanh::lean_ctor_get(v___x_2895_, 3);
                    crate::leanh::lean_inc_ref(v_modules_2896_);
                    crate::leanh::lean_dec_ref(v___x_2895_);
                    v___x_2897_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_2898_ = lean_array_uget_borrowed(v_as_2880_, v_i_2882_);
                    v___x_2899_ = lean_array_get(v___x_2897_, v_modules_2896_, v_a_2898_);
                    crate::leanh::lean_dec_ref(v_modules_2896_);
                    v_toImport_2900_ = crate::leanh::lean_ctor_get(v___x_2899_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_2900_);
                    crate::leanh::lean_dec(v___x_2899_);
                    v_module_2901_ = crate::leanh::lean_ctor_get(v_toImport_2900_, 0);
                    crate::leanh::lean_inc(v_module_2901_);
                    crate::leanh::lean_dec_ref(v_toImport_2900_);
                    v___x_2902_ = 0;
                    crate::leanh::lean_inc(v_declName_2879_);
                    v___x_2903_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(v_module_2901_, v___x_2902_, v_declName_2879_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_);
                    if crate::leanh::lean_obj_tag(v___x_2903_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2903_, 1);
                        v___x_2904_ = crate::leanh::lean_box(0);
                        v___x_2905_ = 1usize;
                        v___x_2906_ = lean_usize_add(v_i_2882_, v___x_2905_);
                        v_i_2882_ = v___x_2906_;
                        v_b_2883_ = v___x_2904_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2879_);
                        return v___x_2903_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5___boxed(
    mut v___x_2908_: *mut crate::leanh::LeanObject,
    mut v_declName_2909_: *mut crate::leanh::LeanObject,
    mut v_as_2910_: *mut crate::leanh::LeanObject,
    mut v_sz_2911_: *mut crate::leanh::LeanObject,
    mut v_i_2912_: *mut crate::leanh::LeanObject,
    mut v_b_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
    mut v___y_2915_: *mut crate::leanh::LeanObject,
    mut v___y_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
    mut v___y_2918_: *mut crate::leanh::LeanObject,
    mut v___y_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
    mut v___y_2922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2923_: usize = 0;
    let mut v_i_boxed_2924_: usize = 0;
    let mut v_res_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2923_ = crate::leanh::lean_unbox_usize(v_sz_2911_);
    crate::leanh::lean_dec(v_sz_2911_);
    v_i_boxed_2924_ = crate::leanh::lean_unbox_usize(v_i_2912_);
    crate::leanh::lean_dec(v_i_2912_);
    v_res_2925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(v___x_2908_, v_declName_2909_, v_as_2910_, v_sz_boxed_2923_, v_i_boxed_2924_, v_b_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_);
    crate::leanh::lean_dec(v___y_2921_);
    crate::leanh::lean_dec_ref(v___y_2920_);
    crate::leanh::lean_dec(v___y_2919_);
    crate::leanh::lean_dec_ref(v___y_2918_);
    crate::leanh::lean_dec(v___y_2917_);
    crate::leanh::lean_dec_ref(v___y_2916_);
    crate::leanh::lean_dec(v___y_2915_);
    crate::leanh::lean_dec_ref(v___y_2914_);
    crate::leanh::lean_dec_ref(v_as_2910_);
    crate::leanh::lean_dec_ref(v___x_2908_);
    return v_res_2925_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2928_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__1;
    v___x_2929_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__0;
    v___x_2930_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2929_,
        v___x_2928_,
    );
    return v___x_2930_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(
    mut v_declName_2933_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2934_: u8,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
    mut v___y_2938_: *mut crate::leanh::LeanObject,
    mut v___y_2939_: *mut crate::leanh::LeanObject,
    mut v___y_2940_: *mut crate::leanh::LeanObject,
    mut v___y_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2952_: usize = 0;
    let mut v___x_2953_: usize = 0;
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_unused_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: u8 = 0;
    let mut v___x_2969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2974_: u8 = 0;
    let mut v_toImport_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: u8 = 0;
    let mut v___x_2986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2944_ = lean_st_ref_get(v___y_2942_);
                v_env_2948_ = crate::leanh::lean_ctor_get(v___x_2944_, 0);
                crate::leanh::lean_inc_ref(v_env_2948_);
                crate::leanh::lean_dec(v___x_2944_);
                v___x_2963_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2948_, v_declName_2933_);
                if crate::leanh::lean_obj_tag(v___x_2963_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_2948_);
                    crate::leanh::lean_dec(v_declName_2933_);
                    state = 1;
                    continue;
                } else {
                    v_val_2964_ = crate::leanh::lean_ctor_get(v___x_2963_, 0);
                    crate::leanh::lean_inc(v_val_2964_);
                    crate::leanh::lean_dec_ref_known(v___x_2963_, 1);
                    v___x_2965_ = l_Lean_Environment_header(v_env_2948_);
                    v_modules_2966_ = crate::leanh::lean_ctor_get(v___x_2965_, 3);
                    crate::leanh::lean_inc_ref(v_modules_2966_);
                    crate::leanh::lean_dec_ref(v___x_2965_);
                    v___x_2967_ = lean_array_get_size(v_modules_2966_);
                    v___x_2968_ = lean_nat_dec_lt(v_val_2964_, v___x_2967_);
                    if v___x_2968_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_2966_);
                        crate::leanh::lean_dec(v_val_2964_);
                        crate::leanh::lean_dec_ref(v_env_2948_);
                        crate::leanh::lean_dec(v_declName_2933_);
                        state = 1;
                        continue;
                    } else {
                        v___x_2969_ = lean_st_ref_get(v___y_2942_);
                        v_env_2970_ = crate::leanh::lean_ctor_get(v___x_2969_, 0);
                        crate::leanh::lean_inc_ref(v_env_2970_);
                        crate::leanh::lean_dec(v___x_2969_);
                        v___x_2971_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__2);
                        v___x_2972_ = lean_array_fget(v_modules_2966_, v_val_2964_);
                        crate::leanh::lean_dec(v_val_2964_);
                        crate::leanh::lean_dec_ref(v_modules_2966_);
                        if v_isMeta_2934_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_2970_);
                            v___y_2974_ = v_isMeta_2934_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_2933_);
                            v___x_2985_ = l_Lean_isMarkedMeta(v_env_2970_, v_declName_2933_);
                            if v___x_2985_ == 0 {
                                v___y_2974_ = v_isMeta_2934_;
                                state = 5;
                                continue;
                            } else {
                                v___x_2986_ = 0;
                                v___y_2974_ = v___x_2986_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2946_ = crate::leanh::lean_box(0);
                v___x_2947_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2947_, 0, v___x_2946_);
                return v___x_2947_;
            }
            2 => {
                v___x_2951_ = crate::leanh::lean_box(0);
                v_sz_2952_ = lean_array_size(v___y_2950_);
                v___x_2953_ = 0usize;
                v___x_2954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__5(v_env_2948_, v_declName_2933_, v___y_2950_, v_sz_2952_, v___x_2953_, v___x_2951_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
                crate::leanh::lean_dec_ref(v___y_2950_);
                crate::leanh::lean_dec_ref(v_env_2948_);
                if crate::leanh::lean_obj_tag(v___x_2954_) == 0 {
                    v_isSharedCheck_2961_ = (!crate::leanh::lean_is_exclusive(v___x_2954_)) as u8;
                    if v_isSharedCheck_2961_ == 0 {
                        v_unused_2962_ = crate::leanh::lean_ctor_get(v___x_2954_, 0);
                        crate::leanh::lean_dec(v_unused_2962_);
                        v___x_2956_ = v___x_2954_;
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2954_);
                        v___x_2956_ = crate::leanh::lean_box(0);
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2954_;
                }
            }
            3 => {
                if v_isShared_2957_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2956_, 0, v___x_2951_);
                    v___x_2959_ = v___x_2956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2951_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2959_;
            }
            5 => {
                v_toImport_2975_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
                crate::leanh::lean_inc_ref(v_toImport_2975_);
                crate::leanh::lean_dec(v___x_2972_);
                v_module_2976_ = crate::leanh::lean_ctor_get(v_toImport_2975_, 0);
                crate::leanh::lean_inc(v_module_2976_);
                crate::leanh::lean_dec_ref(v_toImport_2975_);
                crate::leanh::lean_inc(v_declName_2933_);
                v___x_2977_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4(v_module_2976_, v___y_2974_, v_declName_2933_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
                if crate::leanh::lean_obj_tag(v___x_2977_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2977_, 1);
                    v___x_2978_ = l_Lean_indirectModUseExt;
                    v___x_2979_ = crate::leanh::lean_box(1);
                    v___x_2980_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_2948_);
                    v___x_2981_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_2971_,
                        v___x_2978_,
                        v_env_2948_,
                        v___x_2979_,
                        v___x_2980_,
                    );
                    v___x_2982_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(v___x_2981_, v_declName_2933_);
                    crate::leanh::lean_dec(v___x_2981_);
                    if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                        v___x_2983_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___closed__3;
                        v___y_2950_ = v___x_2983_;
                        state = 2;
                        continue;
                    } else {
                        v_val_2984_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                        crate::leanh::lean_inc(v_val_2984_);
                        crate::leanh::lean_dec_ref_known(v___x_2982_, 1);
                        v___y_2950_ = v_val_2984_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2948_);
                    crate::leanh::lean_dec(v_declName_2933_);
                    return v___x_2977_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2___boxed(
    mut v_declName_2987_: *mut crate::leanh::LeanObject,
    mut v_isMeta_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
    mut v___y_2992_: *mut crate::leanh::LeanObject,
    mut v___y_2993_: *mut crate::leanh::LeanObject,
    mut v___y_2994_: *mut crate::leanh::LeanObject,
    mut v___y_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_2998_: u8 = 0;
    let mut v_res_2999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_2998_ = (crate::leanh::lean_unbox(v_isMeta_2988_) as u8);
    v_res_2999_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(v_declName_2987_, v_isMeta_boxed_2998_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_);
    crate::leanh::lean_dec(v___y_2996_);
    crate::leanh::lean_dec_ref(v___y_2995_);
    crate::leanh::lean_dec(v___y_2994_);
    crate::leanh::lean_dec_ref(v___y_2993_);
    crate::leanh::lean_dec(v___y_2992_);
    crate::leanh::lean_dec_ref(v___y_2991_);
    crate::leanh::lean_dec(v___y_2990_);
    crate::leanh::lean_dec_ref(v___y_2989_);
    return v_res_2999_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(
    mut v_as_x27_3000_: *mut crate::leanh::LeanObject,
    mut v_b_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
    mut v___y_3003_: *mut crate::leanh::LeanObject,
    mut v___y_3004_: *mut crate::leanh::LeanObject,
    mut v___y_3005_: *mut crate::leanh::LeanObject,
    mut v___y_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: u8 = 0;
    let mut v___x_3015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_3000_) == 0 {
                    v___x_3011_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3011_, 0, v_b_3001_);
                    return v___x_3011_;
                } else {
                    v_head_3012_ = crate::leanh::lean_ctor_get(v_as_x27_3000_, 0);
                    v_tail_3013_ = crate::leanh::lean_ctor_get(v_as_x27_3000_, 1);
                    v___x_3014_ = 1;
                    crate::leanh::lean_inc(v_head_3012_);
                    v___x_3015_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2(v_head_3012_, v___x_3014_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_, v___y_3009_);
                    if crate::leanh::lean_obj_tag(v___x_3015_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3015_, 1);
                        v___x_3016_ = crate::leanh::lean_box(0);
                        v_as_x27_3000_ = v_tail_3013_;
                        v_b_3001_ = v___x_3016_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3015_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg___boxed(
    mut v_as_x27_3018_: *mut crate::leanh::LeanObject,
    mut v_b_3019_: *mut crate::leanh::LeanObject,
    mut v___y_3020_: *mut crate::leanh::LeanObject,
    mut v___y_3021_: *mut crate::leanh::LeanObject,
    mut v___y_3022_: *mut crate::leanh::LeanObject,
    mut v___y_3023_: *mut crate::leanh::LeanObject,
    mut v___y_3024_: *mut crate::leanh::LeanObject,
    mut v___y_3025_: *mut crate::leanh::LeanObject,
    mut v___y_3026_: *mut crate::leanh::LeanObject,
    mut v___y_3027_: *mut crate::leanh::LeanObject,
    mut v___y_3028_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3029_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(v_as_x27_3018_, v_b_3019_, v___y_3020_, v___y_3021_, v___y_3022_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
    crate::leanh::lean_dec(v___y_3027_);
    crate::leanh::lean_dec_ref(v___y_3026_);
    crate::leanh::lean_dec(v___y_3025_);
    crate::leanh::lean_dec_ref(v___y_3024_);
    crate::leanh::lean_dec(v___y_3023_);
    crate::leanh::lean_dec_ref(v___y_3022_);
    crate::leanh::lean_dec(v___y_3021_);
    crate::leanh::lean_dec_ref(v___y_3020_);
    crate::leanh::lean_dec(v_as_x27_3018_);
    return v_res_3029_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3030_ = crate::leanh::lean_box(0);
    v___x_3031_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3032_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3032_, 0, v___x_3031_);
    crate::leanh::lean_ctor_set(v___x_3032_, 1, v___x_3030_);
    return v___x_3032_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3034_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___closed__0);
    v___x_3035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3035_, 0, v___x_3034_);
    return v___x_3035_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg___boxed(
    mut v___y_3036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3037_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
    return v_res_3037_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3043_ = l_Lean_maxRecDepthErrorMessage;
    v___x_3044_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3044_, 0, v___x_3043_);
    return v___x_3044_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3045_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__3);
    v___x_3046_ = l_Lean_MessageData_ofFormat(v___x_3045_);
    return v___x_3046_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3047_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__4);
    v___x_3048_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__2;
    v___x_3049_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3049_, 0, v___x_3048_);
    crate::leanh::lean_ctor_set(v___x_3049_, 1, v___x_3047_);
    return v___x_3049_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(
    mut v_ref_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___closed__5);
    v___x_3053_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3053_, 0, v_ref_3050_);
    crate::leanh::lean_ctor_set(v___x_3053_, 1, v___x_3052_);
    v___x_3054_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3054_, 0, v___x_3053_);
    return v___x_3054_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg___boxed(
    mut v_ref_3055_: *mut crate::leanh::LeanObject,
    mut v___y_3056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3057_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(v_ref_3055_);
    return v_res_3057_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(
    mut v_msg_3058_: *mut crate::leanh::LeanObject,
    mut v___y_3059_: *mut crate::leanh::LeanObject,
    mut v___y_3060_: *mut crate::leanh::LeanObject,
    mut v___y_3061_: *mut crate::leanh::LeanObject,
    mut v___y_3062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3069_: u8 = 0;
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3064_ = crate::leanh::lean_ctor_get(v___y_3061_, 5);
                v___x_3065_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0_spec__1(v_msg_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
                v_a_3066_ = crate::leanh::lean_ctor_get(v___x_3065_, 0);
                v_isSharedCheck_3074_ = (!crate::leanh::lean_is_exclusive(v___x_3065_)) as u8;
                if v_isSharedCheck_3074_ == 0 {
                    v___x_3068_ = v___x_3065_;
                    v_isShared_3069_ = v_isSharedCheck_3074_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3066_);
                    crate::leanh::lean_dec(v___x_3065_);
                    v___x_3068_ = crate::leanh::lean_box(0);
                    v_isShared_3069_ = v_isSharedCheck_3074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_3064_);
                v___x_3070_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3070_, 0, v_ref_3064_);
                crate::leanh::lean_ctor_set(v___x_3070_, 1, v_a_3066_);
                if v_isShared_3069_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3068_, 1);
                    crate::leanh::lean_ctor_set(v___x_3068_, 0, v___x_3070_);
                    v___x_3072_ = v___x_3068_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3073_, 0, v___x_3070_);
                    v___x_3072_ = v_reuseFailAlloc_3073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg___boxed(
    mut v_msg_3075_: *mut crate::leanh::LeanObject,
    mut v___y_3076_: *mut crate::leanh::LeanObject,
    mut v___y_3077_: *mut crate::leanh::LeanObject,
    mut v___y_3078_: *mut crate::leanh::LeanObject,
    mut v___y_3079_: *mut crate::leanh::LeanObject,
    mut v___y_3080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3081_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(v_msg_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
    crate::leanh::lean_dec(v___y_3079_);
    crate::leanh::lean_dec_ref(v___y_3078_);
    crate::leanh::lean_dec(v___y_3077_);
    crate::leanh::lean_dec_ref(v___y_3076_);
    return v_res_3081_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(
    mut v_ref_3082_: *mut crate::leanh::LeanObject,
    mut v_msg_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
    mut v___y_3090_: *mut crate::leanh::LeanObject,
    mut v___y_3091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3105_: u8 = 0;
    let mut v_cancelTk_x3f_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3107_: u8 = 0;
    let mut v_inheritedTraceOptions_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_3093_ = crate::leanh::lean_ctor_get(v___y_3090_, 0);
    v_fileMap_3094_ = crate::leanh::lean_ctor_get(v___y_3090_, 1);
    v_options_3095_ = crate::leanh::lean_ctor_get(v___y_3090_, 2);
    v_currRecDepth_3096_ = crate::leanh::lean_ctor_get(v___y_3090_, 3);
    v_maxRecDepth_3097_ = crate::leanh::lean_ctor_get(v___y_3090_, 4);
    v_ref_3098_ = crate::leanh::lean_ctor_get(v___y_3090_, 5);
    v_currNamespace_3099_ = crate::leanh::lean_ctor_get(v___y_3090_, 6);
    v_openDecls_3100_ = crate::leanh::lean_ctor_get(v___y_3090_, 7);
    v_initHeartbeats_3101_ = crate::leanh::lean_ctor_get(v___y_3090_, 8);
    v_maxHeartbeats_3102_ = crate::leanh::lean_ctor_get(v___y_3090_, 9);
    v_quotContext_3103_ = crate::leanh::lean_ctor_get(v___y_3090_, 10);
    v_currMacroScope_3104_ = crate::leanh::lean_ctor_get(v___y_3090_, 11);
    v_diag_3105_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3090_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_3106_ = crate::leanh::lean_ctor_get(v___y_3090_, 12);
    v_suppressElabErrors_3107_ = crate::leanh::lean_ctor_get_uint8(
        v___y_3090_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_3108_ = crate::leanh::lean_ctor_get(v___y_3090_, 13);
    v_ref_3109_ = l_Lean_replaceRef(v_ref_3082_, v_ref_3098_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_3108_);
    crate::leanh::lean_inc(v_cancelTk_x3f_3106_);
    crate::leanh::lean_inc(v_currMacroScope_3104_);
    crate::leanh::lean_inc(v_quotContext_3103_);
    crate::leanh::lean_inc(v_maxHeartbeats_3102_);
    crate::leanh::lean_inc(v_initHeartbeats_3101_);
    crate::leanh::lean_inc(v_openDecls_3100_);
    crate::leanh::lean_inc(v_currNamespace_3099_);
    crate::leanh::lean_inc(v_maxRecDepth_3097_);
    crate::leanh::lean_inc(v_currRecDepth_3096_);
    crate::leanh::lean_inc_ref(v_options_3095_);
    crate::leanh::lean_inc_ref(v_fileMap_3094_);
    crate::leanh::lean_inc_ref(v_fileName_3093_);
    v___x_3110_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_3110_, 0, v_fileName_3093_);
    crate::leanh::lean_ctor_set(v___x_3110_, 1, v_fileMap_3094_);
    crate::leanh::lean_ctor_set(v___x_3110_, 2, v_options_3095_);
    crate::leanh::lean_ctor_set(v___x_3110_, 3, v_currRecDepth_3096_);
    crate::leanh::lean_ctor_set(v___x_3110_, 4, v_maxRecDepth_3097_);
    crate::leanh::lean_ctor_set(v___x_3110_, 5, v_ref_3109_);
    crate::leanh::lean_ctor_set(v___x_3110_, 6, v_currNamespace_3099_);
    crate::leanh::lean_ctor_set(v___x_3110_, 7, v_openDecls_3100_);
    crate::leanh::lean_ctor_set(v___x_3110_, 8, v_initHeartbeats_3101_);
    crate::leanh::lean_ctor_set(v___x_3110_, 9, v_maxHeartbeats_3102_);
    crate::leanh::lean_ctor_set(v___x_3110_, 10, v_quotContext_3103_);
    crate::leanh::lean_ctor_set(v___x_3110_, 11, v_currMacroScope_3104_);
    crate::leanh::lean_ctor_set(v___x_3110_, 12, v_cancelTk_x3f_3106_);
    crate::leanh::lean_ctor_set(v___x_3110_, 13, v_inheritedTraceOptions_3108_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_3110_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_3105_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_3110_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_3107_,
    );
    v___x_3111_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(v_msg_3083_, v___y_3088_, v___y_3089_, v___x_3110_, v___y_3091_);
    crate::leanh::lean_dec_ref_known(v___x_3110_, 14);
    return v___x_3111_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg___boxed(
    mut v_ref_3112_: *mut crate::leanh::LeanObject,
    mut v_msg_3113_: *mut crate::leanh::LeanObject,
    mut v___y_3114_: *mut crate::leanh::LeanObject,
    mut v___y_3115_: *mut crate::leanh::LeanObject,
    mut v___y_3116_: *mut crate::leanh::LeanObject,
    mut v___y_3117_: *mut crate::leanh::LeanObject,
    mut v___y_3118_: *mut crate::leanh::LeanObject,
    mut v___y_3119_: *mut crate::leanh::LeanObject,
    mut v___y_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3123_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(v_ref_3112_, v_msg_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
    crate::leanh::lean_dec(v___y_3121_);
    crate::leanh::lean_dec_ref(v___y_3120_);
    crate::leanh::lean_dec(v___y_3119_);
    crate::leanh::lean_dec_ref(v___y_3118_);
    crate::leanh::lean_dec(v___y_3117_);
    crate::leanh::lean_dec_ref(v___y_3116_);
    crate::leanh::lean_dec(v___y_3115_);
    crate::leanh::lean_dec_ref(v___y_3114_);
    crate::leanh::lean_dec(v_ref_3112_);
    return v_res_3123_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2(
    mut v_env_3124_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_3125_: *mut crate::leanh::LeanObject,
    mut v_openDecls_3126_: *mut crate::leanh::LeanObject,
    mut v_n_3127_: *mut crate::leanh::LeanObject,
    mut v___y_3128_: *mut crate::leanh::LeanObject,
    mut v___y_3129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3130_ = l_Lean_ResolveName_resolveNamespace(
        v_env_3124_,
        v_currNamespace_3125_,
        v_openDecls_3126_,
        v_n_3127_,
    );
    v___x_3131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3131_, 0, v___x_3130_);
    crate::leanh::lean_ctor_set(v___x_3131_, 1, v___y_3129_);
    return v___x_3131_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2___boxed(
    mut v_env_3132_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_3133_: *mut crate::leanh::LeanObject,
    mut v_openDecls_3134_: *mut crate::leanh::LeanObject,
    mut v_n_3135_: *mut crate::leanh::LeanObject,
    mut v___y_3136_: *mut crate::leanh::LeanObject,
    mut v___y_3137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3138_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2(
            v_env_3132_,
            v_currNamespace_3133_,
            v_openDecls_3134_,
            v_n_3135_,
            v___y_3136_,
            v___y_3137_,
        );
    crate::leanh::lean_dec_ref(v___y_3136_);
    return v_res_3138_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(
    mut v_x_3140_: *mut crate::leanh::LeanObject,
    mut v___y_3141_: *mut crate::leanh::LeanObject,
    mut v___y_3142_: *mut crate::leanh::LeanObject,
    mut v___y_3143_: *mut crate::leanh::LeanObject,
    mut v___y_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3190_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_unused_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3207_: u8 = 0;
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3211_: u8 = 0;
    let mut v_reuseFailAlloc_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3213_: u8 = 0;
    let mut v_unused_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3218_: u8 = 0;
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut v_a_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: u8 = 0;
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3150_ = lean_st_ref_get(v___y_3148_);
                v_env_3151_ = crate::leanh::lean_ctor_get(v___x_3150_, 0);
                crate::leanh::lean_inc_ref_n(v_env_3151_, 4);
                crate::leanh::lean_dec(v___x_3150_);
                v_options_3152_ = crate::leanh::lean_ctor_get(v___y_3147_, 2);
                v_currRecDepth_3153_ = crate::leanh::lean_ctor_get(v___y_3147_, 3);
                v_maxRecDepth_3154_ = crate::leanh::lean_ctor_get(v___y_3147_, 4);
                v_ref_3155_ = crate::leanh::lean_ctor_get(v___y_3147_, 5);
                v_currNamespace_3156_ = crate::leanh::lean_ctor_get(v___y_3147_, 6);
                v_openDecls_3157_ = crate::leanh::lean_ctor_get(v___y_3147_, 7);
                v_quotContext_3158_ = crate::leanh::lean_ctor_get(v___y_3147_, 10);
                v_currMacroScope_3159_ = crate::leanh::lean_ctor_get(v___y_3147_, 11);
                v___x_3160_ = lean_st_ref_get(v___y_3148_);
                v_nextMacroScope_3161_ = crate::leanh::lean_ctor_get(v___x_3160_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_3161_);
                crate::leanh::lean_dec(v___x_3160_);
                v___f_3162_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_3162_, 0, v_env_3151_);
                v___f_3163_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_3163_, 0, v_env_3151_);
                crate::leanh::lean_inc_n(v_openDecls_3157_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_3156_, 3);
                v___f_3164_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___f_3164_, 0, v_env_3151_);
                crate::leanh::lean_closure_set(v___f_3164_, 1, v_currNamespace_3156_);
                crate::leanh::lean_closure_set(v___f_3164_, 2, v_openDecls_3157_);
                v___f_3165_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_3165_, 0, v_currNamespace_3156_);
                crate::leanh::lean_inc_ref(v_options_3152_);
                v___f_3166_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                crate::leanh::lean_closure_set(v___f_3166_, 0, v_env_3151_);
                crate::leanh::lean_closure_set(v___f_3166_, 1, v_options_3152_);
                crate::leanh::lean_closure_set(v___f_3166_, 2, v_currNamespace_3156_);
                crate::leanh::lean_closure_set(v___f_3166_, 3, v_openDecls_3157_);
                v_methods_3167_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_methods_3167_, 0, v___f_3162_);
                crate::leanh::lean_ctor_set(v_methods_3167_, 1, v___f_3165_);
                crate::leanh::lean_ctor_set(v_methods_3167_, 2, v___f_3163_);
                crate::leanh::lean_ctor_set(v_methods_3167_, 3, v___f_3164_);
                crate::leanh::lean_ctor_set(v_methods_3167_, 4, v___f_3166_);
                crate::leanh::lean_inc(v_ref_3155_);
                crate::leanh::lean_inc(v_maxRecDepth_3154_);
                crate::leanh::lean_inc(v_currRecDepth_3153_);
                crate::leanh::lean_inc(v_currMacroScope_3159_);
                crate::leanh::lean_inc(v_quotContext_3158_);
                v___x_3168_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3168_, 0, v_methods_3167_);
                crate::leanh::lean_ctor_set(v___x_3168_, 1, v_quotContext_3158_);
                crate::leanh::lean_ctor_set(v___x_3168_, 2, v_currMacroScope_3159_);
                crate::leanh::lean_ctor_set(v___x_3168_, 3, v_currRecDepth_3153_);
                crate::leanh::lean_ctor_set(v___x_3168_, 4, v_maxRecDepth_3154_);
                crate::leanh::lean_ctor_set(v___x_3168_, 5, v_ref_3155_);
                v___x_3169_ = crate::leanh::lean_box(0);
                v___x_3170_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3170_, 0, v_nextMacroScope_3161_);
                crate::leanh::lean_ctor_set(v___x_3170_, 1, v___x_3169_);
                crate::leanh::lean_ctor_set(v___x_3170_, 2, v___x_3169_);
                v___x_3171_ = crate::leanh::lean_apply_2(v_x_3140_, v___x_3168_, v___x_3170_);
                if crate::leanh::lean_obj_tag(v___x_3171_) == 0 {
                    v_a_3172_ = crate::leanh::lean_ctor_get(v___x_3171_, 1);
                    crate::leanh::lean_inc(v_a_3172_);
                    v_a_3173_ = crate::leanh::lean_ctor_get(v___x_3171_, 0);
                    crate::leanh::lean_inc(v_a_3173_);
                    crate::leanh::lean_dec_ref_known(v___x_3171_, 2);
                    v_macroScope_3174_ = crate::leanh::lean_ctor_get(v_a_3172_, 0);
                    crate::leanh::lean_inc(v_macroScope_3174_);
                    v_traceMsgs_3175_ = crate::leanh::lean_ctor_get(v_a_3172_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_3175_);
                    v_expandedMacroDecls_3176_ = crate::leanh::lean_ctor_get(v_a_3172_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_3176_);
                    crate::leanh::lean_dec(v_a_3172_);
                    v___x_3177_ = crate::leanh::lean_box(0);
                    v___x_3178_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(v_expandedMacroDecls_3176_, v___x_3177_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_3176_);
                    if crate::leanh::lean_obj_tag(v___x_3178_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3178_, 1);
                        v___x_3179_ = lean_st_ref_take(v___y_3148_);
                        v_env_3180_ = crate::leanh::lean_ctor_get(v___x_3179_, 0);
                        v_ngen_3181_ = crate::leanh::lean_ctor_get(v___x_3179_, 2);
                        v_auxDeclNGen_3182_ = crate::leanh::lean_ctor_get(v___x_3179_, 3);
                        v_traceState_3183_ = crate::leanh::lean_ctor_get(v___x_3179_, 4);
                        v_cache_3184_ = crate::leanh::lean_ctor_get(v___x_3179_, 5);
                        v_messages_3185_ = crate::leanh::lean_ctor_get(v___x_3179_, 6);
                        v_infoState_3186_ = crate::leanh::lean_ctor_get(v___x_3179_, 7);
                        v_snapshotTasks_3187_ = crate::leanh::lean_ctor_get(v___x_3179_, 8);
                        v_isSharedCheck_3213_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3179_)) as u8;
                        if v_isSharedCheck_3213_ == 0 {
                            v_unused_3214_ = crate::leanh::lean_ctor_get(v___x_3179_, 1);
                            crate::leanh::lean_dec(v_unused_3214_);
                            v___x_3189_ = v___x_3179_;
                            v_isShared_3190_ = v_isSharedCheck_3213_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_3187_);
                            crate::leanh::lean_inc(v_infoState_3186_);
                            crate::leanh::lean_inc(v_messages_3185_);
                            crate::leanh::lean_inc(v_cache_3184_);
                            crate::leanh::lean_inc(v_traceState_3183_);
                            crate::leanh::lean_inc(v_auxDeclNGen_3182_);
                            crate::leanh::lean_inc(v_ngen_3181_);
                            crate::leanh::lean_inc(v_env_3180_);
                            crate::leanh::lean_dec(v___x_3179_);
                            v___x_3189_ = crate::leanh::lean_box(0);
                            v_isShared_3190_ = v_isSharedCheck_3213_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_3175_);
                        crate::leanh::lean_dec(v_macroScope_3174_);
                        crate::leanh::lean_dec(v_a_3173_);
                        v_a_3215_ = crate::leanh::lean_ctor_get(v___x_3178_, 0);
                        v_isSharedCheck_3222_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3178_)) as u8;
                        if v_isSharedCheck_3222_ == 0 {
                            v___x_3217_ = v___x_3178_;
                            v_isShared_3218_ = v_isSharedCheck_3222_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3215_);
                            crate::leanh::lean_dec(v___x_3178_);
                            v___x_3217_ = crate::leanh::lean_box(0);
                            v_isShared_3218_ = v_isSharedCheck_3222_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_3223_ = crate::leanh::lean_ctor_get(v___x_3171_, 0);
                    crate::leanh::lean_inc(v_a_3223_);
                    crate::leanh::lean_dec_ref_known(v___x_3171_, 2);
                    if crate::leanh::lean_obj_tag(v_a_3223_) == 0 {
                        v_a_3224_ = crate::leanh::lean_ctor_get(v_a_3223_, 0);
                        crate::leanh::lean_inc(v_a_3224_);
                        v_a_3225_ = crate::leanh::lean_ctor_get(v_a_3223_, 1);
                        crate::leanh::lean_inc_ref(v_a_3225_);
                        crate::leanh::lean_dec_ref_known(v_a_3223_, 2);
                        v___x_3226_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___closed__0;
                        v___x_3227_ = lean_string_dec_eq(v_a_3225_, v___x_3226_);
                        if v___x_3227_ == 0 {
                            v___x_3228_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3228_, 0, v_a_3225_);
                            v___x_3229_ = l_Lean_MessageData_ofFormat(v___x_3228_);
                            v___x_3230_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(v_a_3224_, v___x_3229_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
                            crate::leanh::lean_dec(v_a_3224_);
                            return v___x_3230_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_3225_);
                            v___x_3231_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(v_a_3224_);
                            return v___x_3231_;
                        }
                    } else {
                        v___x_3232_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
                        return v___x_3232_;
                    }
                }
            }
            1 => {
                if v_isShared_3190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3189_, 1, v_macroScope_3174_);
                    v___x_3192_ = v___x_3189_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3212_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_env_3180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 1, v_macroScope_3174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 2, v_ngen_3181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 3, v_auxDeclNGen_3182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 4, v_traceState_3183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 5, v_cache_3184_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 6, v_messages_3185_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 7, v_infoState_3186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3212_, 8, v_snapshotTasks_3187_);
                    v___x_3192_ = v_reuseFailAlloc_3212_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3193_ = lean_st_ref_set(v___y_3148_, v___x_3192_);
                v___x_3194_ = l_List_reverse___redArg(v_traceMsgs_3175_);
                v___x_3195_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__4(v___x_3194_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
                if crate::leanh::lean_obj_tag(v___x_3195_) == 0 {
                    v_isSharedCheck_3202_ = (!crate::leanh::lean_is_exclusive(v___x_3195_)) as u8;
                    if v_isSharedCheck_3202_ == 0 {
                        v_unused_3203_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                        crate::leanh::lean_dec(v_unused_3203_);
                        v___x_3197_ = v___x_3195_;
                        v_isShared_3198_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3195_);
                        v___x_3197_ = crate::leanh::lean_box(0);
                        v_isShared_3198_ = v_isSharedCheck_3202_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3173_);
                    v_a_3204_ = crate::leanh::lean_ctor_get(v___x_3195_, 0);
                    v_isSharedCheck_3211_ = (!crate::leanh::lean_is_exclusive(v___x_3195_)) as u8;
                    if v_isSharedCheck_3211_ == 0 {
                        v___x_3206_ = v___x_3195_;
                        v_isShared_3207_ = v_isSharedCheck_3211_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3204_);
                        crate::leanh::lean_dec(v___x_3195_);
                        v___x_3206_ = crate::leanh::lean_box(0);
                        v_isShared_3207_ = v_isSharedCheck_3211_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3197_, 0, v_a_3173_);
                    v___x_3200_ = v___x_3197_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3173_);
                    v___x_3200_ = v_reuseFailAlloc_3201_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3200_;
            }
            5 => {
                if v_isShared_3207_ == 0 {
                    v___x_3209_ = v___x_3206_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
                    v___x_3209_ = v_reuseFailAlloc_3210_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3209_;
            }
            7 => {
                if v_isShared_3218_ == 0 {
                    v___x_3220_ = v___x_3217_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3220_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg___boxed(
    mut v_x_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
    mut v___y_3235_: *mut crate::leanh::LeanObject,
    mut v___y_3236_: *mut crate::leanh::LeanObject,
    mut v___y_3237_: *mut crate::leanh::LeanObject,
    mut v___y_3238_: *mut crate::leanh::LeanObject,
    mut v___y_3239_: *mut crate::leanh::LeanObject,
    mut v___y_3240_: *mut crate::leanh::LeanObject,
    mut v___y_3241_: *mut crate::leanh::LeanObject,
    mut v___y_3242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3243_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(
        v_x_3233_,
        v___y_3234_,
        v___y_3235_,
        v___y_3236_,
        v___y_3237_,
        v___y_3238_,
        v___y_3239_,
        v___y_3240_,
        v___y_3241_,
    );
    crate::leanh::lean_dec(v___y_3241_);
    crate::leanh::lean_dec_ref(v___y_3240_);
    crate::leanh::lean_dec(v___y_3239_);
    crate::leanh::lean_dec_ref(v___y_3238_);
    crate::leanh::lean_dec(v___y_3237_);
    crate::leanh::lean_dec_ref(v___y_3236_);
    crate::leanh::lean_dec(v___y_3235_);
    crate::leanh::lean_dec_ref(v___y_3234_);
    return v_res_3243_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0(
    mut v_stx_3244_: *mut crate::leanh::LeanObject,
    mut v_output_3245_: *mut crate::leanh::LeanObject,
    mut v_trees_3246_: *mut crate::leanh::LeanObject,
    mut v___y_3247_: *mut crate::leanh::LeanObject,
    mut v___y_3248_: *mut crate::leanh::LeanObject,
    mut v___y_3249_: *mut crate::leanh::LeanObject,
    mut v___y_3250_: *mut crate::leanh::LeanObject,
    mut v___y_3251_: *mut crate::leanh::LeanObject,
    mut v___y_3252_: *mut crate::leanh::LeanObject,
    mut v___y_3253_: *mut crate::leanh::LeanObject,
    mut v___y_3254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_3256_ = crate::leanh::lean_ctor_get(v___y_3251_, 2);
    crate::leanh::lean_inc_ref(v_lctx_3256_);
    v___x_3257_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3257_, 0, v_lctx_3256_);
    crate::leanh::lean_ctor_set(v___x_3257_, 1, v_stx_3244_);
    crate::leanh::lean_ctor_set(v___x_3257_, 2, v_output_3245_);
    v___x_3258_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3258_, 0, v___x_3257_);
    v___x_3259_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3258_);
    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_trees_3246_);
    v___x_3260_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3260_, 0, v___x_3259_);
    return v___x_3260_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0___boxed(
    mut v_stx_3261_: *mut crate::leanh::LeanObject,
    mut v_output_3262_: *mut crate::leanh::LeanObject,
    mut v_trees_3263_: *mut crate::leanh::LeanObject,
    mut v___y_3264_: *mut crate::leanh::LeanObject,
    mut v___y_3265_: *mut crate::leanh::LeanObject,
    mut v___y_3266_: *mut crate::leanh::LeanObject,
    mut v___y_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3273_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0(v_stx_3261_, v_output_3262_, v_trees_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
    crate::leanh::lean_dec(v___y_3271_);
    crate::leanh::lean_dec_ref(v___y_3270_);
    crate::leanh::lean_dec(v___y_3269_);
    crate::leanh::lean_dec_ref(v___y_3268_);
    crate::leanh::lean_dec(v___y_3267_);
    crate::leanh::lean_dec_ref(v___y_3266_);
    crate::leanh::lean_dec(v___y_3265_);
    crate::leanh::lean_dec_ref(v___y_3264_);
    return v_res_3273_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(
    mut v___y_3274_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_3275_: *mut crate::leanh::LeanObject,
    mut v___y_3276_: *mut crate::leanh::LeanObject,
    mut v___y_3277_: *mut crate::leanh::LeanObject,
    mut v___y_3278_: *mut crate::leanh::LeanObject,
    mut v___y_3279_: *mut crate::leanh::LeanObject,
    mut v___y_3280_: *mut crate::leanh::LeanObject,
    mut v___y_3281_: *mut crate::leanh::LeanObject,
    mut v___y_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3293_: u8 = 0;
    let mut v___x_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3306_: u8 = 0;
    let mut v_enabled_3307_: u8 = 0;
    let mut v_assignment_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3312_: u8 = 0;
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3325_: u8 = 0;
    let mut v_unused_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3327_: u8 = 0;
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_a_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3332_: u8 = 0;
    let mut v___x_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3286_ = lean_st_ref_get(v___y_3274_);
                v_infoState_3287_ = crate::leanh::lean_ctor_get(v___x_3286_, 7);
                crate::leanh::lean_inc_ref(v_infoState_3287_);
                crate::leanh::lean_dec(v___x_3286_);
                v_trees_3288_ = crate::leanh::lean_ctor_get(v_infoState_3287_, 2);
                crate::leanh::lean_inc_ref(v_trees_3288_);
                crate::leanh::lean_dec_ref(v_infoState_3287_);
                crate::leanh::lean_inc(v___y_3274_);
                crate::leanh::lean_inc_ref(v___y_3282_);
                crate::leanh::lean_inc(v___y_3281_);
                crate::leanh::lean_inc_ref(v___y_3280_);
                crate::leanh::lean_inc(v___y_3279_);
                crate::leanh::lean_inc_ref(v___y_3278_);
                crate::leanh::lean_inc(v___y_3277_);
                crate::leanh::lean_inc_ref(v___y_3276_);
                v___x_3289_ = crate::leanh::lean_apply_10(
                    v_mkInfoTree_3275_,
                    v_trees_3288_,
                    v___y_3276_,
                    v___y_3277_,
                    v___y_3278_,
                    v___y_3279_,
                    v___y_3280_,
                    v___y_3281_,
                    v___y_3282_,
                    v___y_3274_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3289_) == 0 {
                    v_a_3290_ = crate::leanh::lean_ctor_get(v___x_3289_, 0);
                    v_isSharedCheck_3328_ = (!crate::leanh::lean_is_exclusive(v___x_3289_)) as u8;
                    if v_isSharedCheck_3328_ == 0 {
                        v___x_3292_ = v___x_3289_;
                        v_isShared_3293_ = v_isSharedCheck_3328_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3290_);
                        crate::leanh::lean_dec(v___x_3289_);
                        v___x_3292_ = crate::leanh::lean_box(0);
                        v_isShared_3293_ = v_isSharedCheck_3328_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_3283_);
                    v_a_3329_ = crate::leanh::lean_ctor_get(v___x_3289_, 0);
                    v_isSharedCheck_3336_ = (!crate::leanh::lean_is_exclusive(v___x_3289_)) as u8;
                    if v_isSharedCheck_3336_ == 0 {
                        v___x_3331_ = v___x_3289_;
                        v_isShared_3332_ = v_isSharedCheck_3336_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3329_);
                        crate::leanh::lean_dec(v___x_3289_);
                        v___x_3331_ = crate::leanh::lean_box(0);
                        v_isShared_3332_ = v_isSharedCheck_3336_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3294_ = lean_st_ref_take(v___y_3274_);
                v_infoState_3295_ = crate::leanh::lean_ctor_get(v___x_3294_, 7);
                v_env_3296_ = crate::leanh::lean_ctor_get(v___x_3294_, 0);
                v_nextMacroScope_3297_ = crate::leanh::lean_ctor_get(v___x_3294_, 1);
                v_ngen_3298_ = crate::leanh::lean_ctor_get(v___x_3294_, 2);
                v_auxDeclNGen_3299_ = crate::leanh::lean_ctor_get(v___x_3294_, 3);
                v_traceState_3300_ = crate::leanh::lean_ctor_get(v___x_3294_, 4);
                v_cache_3301_ = crate::leanh::lean_ctor_get(v___x_3294_, 5);
                v_messages_3302_ = crate::leanh::lean_ctor_get(v___x_3294_, 6);
                v_snapshotTasks_3303_ = crate::leanh::lean_ctor_get(v___x_3294_, 8);
                v_isSharedCheck_3327_ = (!crate::leanh::lean_is_exclusive(v___x_3294_)) as u8;
                if v_isSharedCheck_3327_ == 0 {
                    v___x_3305_ = v___x_3294_;
                    v_isShared_3306_ = v_isSharedCheck_3327_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3303_);
                    crate::leanh::lean_inc(v_infoState_3295_);
                    crate::leanh::lean_inc(v_messages_3302_);
                    crate::leanh::lean_inc(v_cache_3301_);
                    crate::leanh::lean_inc(v_traceState_3300_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3299_);
                    crate::leanh::lean_inc(v_ngen_3298_);
                    crate::leanh::lean_inc(v_nextMacroScope_3297_);
                    crate::leanh::lean_inc(v_env_3296_);
                    crate::leanh::lean_dec(v___x_3294_);
                    v___x_3305_ = crate::leanh::lean_box(0);
                    v_isShared_3306_ = v_isSharedCheck_3327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_enabled_3307_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3295_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_3308_ = crate::leanh::lean_ctor_get(v_infoState_3295_, 0);
                v_lazyAssignment_3309_ = crate::leanh::lean_ctor_get(v_infoState_3295_, 1);
                v_isSharedCheck_3325_ = (!crate::leanh::lean_is_exclusive(v_infoState_3295_)) as u8;
                if v_isSharedCheck_3325_ == 0 {
                    v_unused_3326_ = crate::leanh::lean_ctor_get(v_infoState_3295_, 2);
                    crate::leanh::lean_dec(v_unused_3326_);
                    v___x_3311_ = v_infoState_3295_;
                    v_isShared_3312_ = v_isSharedCheck_3325_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_3309_);
                    crate::leanh::lean_inc(v_assignment_3308_);
                    crate::leanh::lean_dec(v_infoState_3295_);
                    v___x_3311_ = crate::leanh::lean_box(0);
                    v_isShared_3312_ = v_isSharedCheck_3325_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3313_ = l_Lean_PersistentArray_push___redArg(v_a_3283_, v_a_3290_);
                if v_isShared_3312_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3311_, 2, v___x_3313_);
                    v___x_3315_ = v___x_3311_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3324_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_assignment_3308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_lazyAssignment_3309_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3324_, 2, v___x_3313_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3324_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_3307_,
                    );
                    v___x_3315_ = v_reuseFailAlloc_3324_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3305_, 7, v___x_3315_);
                    v___x_3317_ = v___x_3305_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3323_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_env_3296_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 1, v_nextMacroScope_3297_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 2, v_ngen_3298_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 3, v_auxDeclNGen_3299_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 4, v_traceState_3300_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 5, v_cache_3301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 6, v_messages_3302_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 7, v___x_3315_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3323_, 8, v_snapshotTasks_3303_);
                    v___x_3317_ = v_reuseFailAlloc_3323_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3318_ = lean_st_ref_set(v___y_3274_, v___x_3317_);
                v___x_3319_ = crate::leanh::lean_box(0);
                if v_isShared_3293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3292_, 0, v___x_3319_);
                    v___x_3321_ = v___x_3292_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3322_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
                    v___x_3321_ = v_reuseFailAlloc_3322_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3321_;
            }
            7 => {
                if v_isShared_3332_ == 0 {
                    v___x_3334_ = v___x_3331_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3335_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
                    v___x_3334_ = v_reuseFailAlloc_3335_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0___boxed(
    mut v___y_3337_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_3338_: *mut crate::leanh::LeanObject,
    mut v___y_3339_: *mut crate::leanh::LeanObject,
    mut v___y_3340_: *mut crate::leanh::LeanObject,
    mut v___y_3341_: *mut crate::leanh::LeanObject,
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
    mut v_a_3346_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(v___y_3337_, v_mkInfoTree_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v_a_3346_, v_a_x3f_3347_);
    crate::leanh::lean_dec(v_a_x3f_3347_);
    crate::leanh::lean_dec_ref(v___y_3345_);
    crate::leanh::lean_dec(v___y_3344_);
    crate::leanh::lean_dec_ref(v___y_3343_);
    crate::leanh::lean_dec(v___y_3342_);
    crate::leanh::lean_dec_ref(v___y_3341_);
    crate::leanh::lean_dec(v___y_3340_);
    crate::leanh::lean_dec_ref(v___y_3339_);
    crate::leanh::lean_dec(v___y_3337_);
    return v_res_3349_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3350_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3351_ = lean_mk_empty_array_with_capacity(v___x_3350_);
    v___x_3352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3352_, 0, v___x_3351_);
    return v___x_3352_;
}
pub unsafe fn _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3353_: usize = 0;
    let mut v___x_3354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3353_ = 5usize;
    v___x_3354_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3355_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3356_ = lean_mk_empty_array_with_capacity(v___x_3355_);
    v___x_3357_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__0);
    v___x_3358_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3358_, 0, v___x_3357_);
    crate::leanh::lean_ctor_set(v___x_3358_, 1, v___x_3356_);
    crate::leanh::lean_ctor_set(v___x_3358_, 2, v___x_3354_);
    crate::leanh::lean_ctor_set(v___x_3358_, 3, v___x_3354_);
    crate::leanh::lean_ctor_set_usize(v___x_3358_, 4, v___x_3353_);
    return v___x_3358_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(
    mut v___y_3359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3376_: u8 = 0;
    let mut v_enabled_3377_: u8 = 0;
    let mut v_assignment_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3382_: u8 = 0;
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_unused_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3394_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3361_ = lean_st_ref_get(v___y_3359_);
                v_infoState_3362_ = crate::leanh::lean_ctor_get(v___x_3361_, 7);
                crate::leanh::lean_inc_ref(v_infoState_3362_);
                crate::leanh::lean_dec(v___x_3361_);
                v_trees_3363_ = crate::leanh::lean_ctor_get(v_infoState_3362_, 2);
                crate::leanh::lean_inc_ref(v_trees_3363_);
                crate::leanh::lean_dec_ref(v_infoState_3362_);
                v___x_3364_ = lean_st_ref_take(v___y_3359_);
                v_infoState_3365_ = crate::leanh::lean_ctor_get(v___x_3364_, 7);
                v_env_3366_ = crate::leanh::lean_ctor_get(v___x_3364_, 0);
                v_nextMacroScope_3367_ = crate::leanh::lean_ctor_get(v___x_3364_, 1);
                v_ngen_3368_ = crate::leanh::lean_ctor_get(v___x_3364_, 2);
                v_auxDeclNGen_3369_ = crate::leanh::lean_ctor_get(v___x_3364_, 3);
                v_traceState_3370_ = crate::leanh::lean_ctor_get(v___x_3364_, 4);
                v_cache_3371_ = crate::leanh::lean_ctor_get(v___x_3364_, 5);
                v_messages_3372_ = crate::leanh::lean_ctor_get(v___x_3364_, 6);
                v_snapshotTasks_3373_ = crate::leanh::lean_ctor_get(v___x_3364_, 8);
                v_isSharedCheck_3394_ = (!crate::leanh::lean_is_exclusive(v___x_3364_)) as u8;
                if v_isSharedCheck_3394_ == 0 {
                    v___x_3375_ = v___x_3364_;
                    v_isShared_3376_ = v_isSharedCheck_3394_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3373_);
                    crate::leanh::lean_inc(v_infoState_3365_);
                    crate::leanh::lean_inc(v_messages_3372_);
                    crate::leanh::lean_inc(v_cache_3371_);
                    crate::leanh::lean_inc(v_traceState_3370_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3369_);
                    crate::leanh::lean_inc(v_ngen_3368_);
                    crate::leanh::lean_inc(v_nextMacroScope_3367_);
                    crate::leanh::lean_inc(v_env_3366_);
                    crate::leanh::lean_dec(v___x_3364_);
                    v___x_3375_ = crate::leanh::lean_box(0);
                    v_isShared_3376_ = v_isSharedCheck_3394_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_enabled_3377_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3365_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_3378_ = crate::leanh::lean_ctor_get(v_infoState_3365_, 0);
                v_lazyAssignment_3379_ = crate::leanh::lean_ctor_get(v_infoState_3365_, 1);
                v_isSharedCheck_3392_ = (!crate::leanh::lean_is_exclusive(v_infoState_3365_)) as u8;
                if v_isSharedCheck_3392_ == 0 {
                    v_unused_3393_ = crate::leanh::lean_ctor_get(v_infoState_3365_, 2);
                    crate::leanh::lean_dec(v_unused_3393_);
                    v___x_3381_ = v_infoState_3365_;
                    v_isShared_3382_ = v_isSharedCheck_3392_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lazyAssignment_3379_);
                    crate::leanh::lean_inc(v_assignment_3378_);
                    crate::leanh::lean_dec(v_infoState_3365_);
                    v___x_3381_ = crate::leanh::lean_box(0);
                    v_isShared_3382_ = v_isSharedCheck_3392_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3383_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1_once), _init_l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___closed__1);
                if v_isShared_3382_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3381_, 2, v___x_3383_);
                    v___x_3385_ = v___x_3381_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_assignment_3378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_lazyAssignment_3379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 2, v___x_3383_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3391_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_3377_,
                    );
                    v___x_3385_ = v_reuseFailAlloc_3391_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3376_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3375_, 7, v___x_3385_);
                    v___x_3387_ = v___x_3375_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_env_3366_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 1, v_nextMacroScope_3367_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 2, v_ngen_3368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 3, v_auxDeclNGen_3369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 4, v_traceState_3370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 5, v_cache_3371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 6, v_messages_3372_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 7, v___x_3385_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 8, v_snapshotTasks_3373_);
                    v___x_3387_ = v_reuseFailAlloc_3390_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3388_ = lean_st_ref_set(v___y_3359_, v___x_3387_);
                v___x_3389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3389_, 0, v_trees_3363_);
                return v___x_3389_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg___boxed(
    mut v___y_3395_: *mut crate::leanh::LeanObject,
    mut v___y_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(v___y_3395_);
    crate::leanh::lean_dec(v___y_3395_);
    return v_res_3397_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(
    mut v_x_3398_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
    mut v___y_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_3411_: u8 = 0;
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3419_: u8 = 0;
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3425_: u8 = 0;
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3429_: u8 = 0;
    let mut v_unused_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3434_: u8 = 0;
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3438_: u8 = 0;
    let mut v_reuseFailAlloc_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3440_: u8 = 0;
    let mut v_a_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3446_: u8 = 0;
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3450_: u8 = 0;
    let mut v_unused_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3455_: u8 = 0;
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3409_ = lean_st_ref_get(v___y_3407_);
                v_infoState_3410_ = crate::leanh::lean_ctor_get(v___x_3409_, 7);
                crate::leanh::lean_inc_ref(v_infoState_3410_);
                crate::leanh::lean_dec(v___x_3409_);
                v_enabled_3411_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_3410_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_3410_);
                if v_enabled_3411_ == 0 {
                    crate::leanh::lean_dec_ref(v_mkInfoTree_3399_);
                    crate::leanh::lean_inc(v___y_3407_);
                    crate::leanh::lean_inc_ref(v___y_3406_);
                    crate::leanh::lean_inc(v___y_3405_);
                    crate::leanh::lean_inc_ref(v___y_3404_);
                    crate::leanh::lean_inc(v___y_3403_);
                    crate::leanh::lean_inc_ref(v___y_3402_);
                    crate::leanh::lean_inc(v___y_3401_);
                    crate::leanh::lean_inc_ref(v___y_3400_);
                    v___x_3412_ = crate::leanh::lean_apply_9(
                        v_x_3398_,
                        v___y_3400_,
                        v___y_3401_,
                        v___y_3402_,
                        v___y_3403_,
                        v___y_3404_,
                        v___y_3405_,
                        v___y_3406_,
                        v___y_3407_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_3412_;
                } else {
                    v___x_3413_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(v___y_3407_);
                    v_a_3414_ = crate::leanh::lean_ctor_get(v___x_3413_, 0);
                    crate::leanh::lean_inc(v_a_3414_);
                    crate::leanh::lean_dec_ref(v___x_3413_);
                    crate::leanh::lean_inc(v___y_3407_);
                    crate::leanh::lean_inc_ref(v___y_3406_);
                    crate::leanh::lean_inc(v___y_3405_);
                    crate::leanh::lean_inc_ref(v___y_3404_);
                    crate::leanh::lean_inc(v___y_3403_);
                    crate::leanh::lean_inc_ref(v___y_3402_);
                    crate::leanh::lean_inc(v___y_3401_);
                    crate::leanh::lean_inc_ref(v___y_3400_);
                    v_r_3415_ = crate::leanh::lean_apply_9(
                        v_x_3398_,
                        v___y_3400_,
                        v___y_3401_,
                        v___y_3402_,
                        v___y_3403_,
                        v___y_3404_,
                        v___y_3405_,
                        v___y_3406_,
                        v___y_3407_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v_r_3415_) == 0 {
                        v_a_3416_ = crate::leanh::lean_ctor_get(v_r_3415_, 0);
                        v_isSharedCheck_3440_ = (!crate::leanh::lean_is_exclusive(v_r_3415_)) as u8;
                        if v_isSharedCheck_3440_ == 0 {
                            v___x_3418_ = v_r_3415_;
                            v_isShared_3419_ = v_isSharedCheck_3440_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3416_);
                            crate::leanh::lean_dec(v_r_3415_);
                            v___x_3418_ = crate::leanh::lean_box(0);
                            v_isShared_3419_ = v_isSharedCheck_3440_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3441_ = crate::leanh::lean_ctor_get(v_r_3415_, 0);
                        crate::leanh::lean_inc(v_a_3441_);
                        crate::leanh::lean_dec_ref_known(v_r_3415_, 1);
                        v___x_3442_ = crate::leanh::lean_box(0);
                        v___x_3443_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(v___y_3407_, v_mkInfoTree_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v_a_3414_, v___x_3442_);
                        if crate::leanh::lean_obj_tag(v___x_3443_) == 0 {
                            v_isSharedCheck_3450_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3443_)) as u8;
                            if v_isSharedCheck_3450_ == 0 {
                                v_unused_3451_ = crate::leanh::lean_ctor_get(v___x_3443_, 0);
                                crate::leanh::lean_dec(v_unused_3451_);
                                v___x_3445_ = v___x_3443_;
                                v_isShared_3446_ = v_isSharedCheck_3450_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3443_);
                                v___x_3445_ = crate::leanh::lean_box(0);
                                v_isShared_3446_ = v_isSharedCheck_3450_;
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3441_);
                            v_a_3452_ = crate::leanh::lean_ctor_get(v___x_3443_, 0);
                            v_isSharedCheck_3459_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3443_)) as u8;
                            if v_isSharedCheck_3459_ == 0 {
                                v___x_3454_ = v___x_3443_;
                                v_isShared_3455_ = v_isSharedCheck_3459_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3452_);
                                crate::leanh::lean_dec(v___x_3443_);
                                v___x_3454_ = crate::leanh::lean_box(0);
                                v_isShared_3455_ = v_isSharedCheck_3459_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_3416_);
                if v_isShared_3419_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3418_, 1);
                    v___x_3421_ = v___x_3418_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3439_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3416_);
                    v___x_3421_ = v_reuseFailAlloc_3439_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3422_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___lam__0(v___y_3407_, v_mkInfoTree_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v_a_3414_, v___x_3421_);
                crate::leanh::lean_dec_ref(v___x_3421_);
                if crate::leanh::lean_obj_tag(v___x_3422_) == 0 {
                    v_isSharedCheck_3429_ = (!crate::leanh::lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3429_ == 0 {
                        v_unused_3430_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
                        crate::leanh::lean_dec(v_unused_3430_);
                        v___x_3424_ = v___x_3422_;
                        v_isShared_3425_ = v_isSharedCheck_3429_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3422_);
                        v___x_3424_ = crate::leanh::lean_box(0);
                        v_isShared_3425_ = v_isSharedCheck_3429_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3416_);
                    v_a_3431_ = crate::leanh::lean_ctor_get(v___x_3422_, 0);
                    v_isSharedCheck_3438_ = (!crate::leanh::lean_is_exclusive(v___x_3422_)) as u8;
                    if v_isSharedCheck_3438_ == 0 {
                        v___x_3433_ = v___x_3422_;
                        v_isShared_3434_ = v_isSharedCheck_3438_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3431_);
                        crate::leanh::lean_dec(v___x_3422_);
                        v___x_3433_ = crate::leanh::lean_box(0);
                        v_isShared_3434_ = v_isSharedCheck_3438_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3424_, 0, v_a_3416_);
                    v___x_3427_ = v___x_3424_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3428_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3428_, 0, v_a_3416_);
                    v___x_3427_ = v_reuseFailAlloc_3428_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3427_;
            }
            5 => {
                if v_isShared_3434_ == 0 {
                    v___x_3436_ = v___x_3433_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3437_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_a_3431_);
                    v___x_3436_ = v_reuseFailAlloc_3437_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3436_;
            }
            7 => {
                if v_isShared_3446_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3445_, 1);
                    crate::leanh::lean_ctor_set(v___x_3445_, 0, v_a_3441_);
                    v___x_3448_ = v___x_3445_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3449_, 0, v_a_3441_);
                    v___x_3448_ = v_reuseFailAlloc_3449_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3448_;
            }
            9 => {
                if v_isShared_3455_ == 0 {
                    v___x_3457_ = v___x_3454_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3458_, 0, v_a_3452_);
                    v___x_3457_ = v_reuseFailAlloc_3458_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg___boxed(
    mut v_x_3460_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_3461_: *mut crate::leanh::LeanObject,
    mut v___y_3462_: *mut crate::leanh::LeanObject,
    mut v___y_3463_: *mut crate::leanh::LeanObject,
    mut v___y_3464_: *mut crate::leanh::LeanObject,
    mut v___y_3465_: *mut crate::leanh::LeanObject,
    mut v___y_3466_: *mut crate::leanh::LeanObject,
    mut v___y_3467_: *mut crate::leanh::LeanObject,
    mut v___y_3468_: *mut crate::leanh::LeanObject,
    mut v___y_3469_: *mut crate::leanh::LeanObject,
    mut v___y_3470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3471_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(v_x_3460_, v_mkInfoTree_3461_, v___y_3462_, v___y_3463_, v___y_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
    crate::leanh::lean_dec(v___y_3469_);
    crate::leanh::lean_dec_ref(v___y_3468_);
    crate::leanh::lean_dec(v___y_3467_);
    crate::leanh::lean_dec_ref(v___y_3466_);
    crate::leanh::lean_dec(v___y_3465_);
    crate::leanh::lean_dec_ref(v___y_3464_);
    crate::leanh::lean_dec(v___y_3463_);
    crate::leanh::lean_dec_ref(v___y_3462_);
    return v_res_3471_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(
    mut v_stx_3472_: *mut crate::leanh::LeanObject,
    mut v_output_3473_: *mut crate::leanh::LeanObject,
    mut v_x_3474_: *mut crate::leanh::LeanObject,
    mut v___y_3475_: *mut crate::leanh::LeanObject,
    mut v___y_3476_: *mut crate::leanh::LeanObject,
    mut v___y_3477_: *mut crate::leanh::LeanObject,
    mut v___y_3478_: *mut crate::leanh::LeanObject,
    mut v___y_3479_: *mut crate::leanh::LeanObject,
    mut v___y_3480_: *mut crate::leanh::LeanObject,
    mut v___y_3481_: *mut crate::leanh::LeanObject,
    mut v___y_3482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_3484_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 2);
    crate::leanh::lean_closure_set(v___f_3484_, 0, v_stx_3472_);
    crate::leanh::lean_closure_set(v___f_3484_, 1, v_output_3473_);
    v___x_3485_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(v_x_3474_, v___f_3484_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_, v___y_3481_, v___y_3482_);
    return v___x_3485_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg___boxed(
    mut v_stx_3486_: *mut crate::leanh::LeanObject,
    mut v_output_3487_: *mut crate::leanh::LeanObject,
    mut v_x_3488_: *mut crate::leanh::LeanObject,
    mut v___y_3489_: *mut crate::leanh::LeanObject,
    mut v___y_3490_: *mut crate::leanh::LeanObject,
    mut v___y_3491_: *mut crate::leanh::LeanObject,
    mut v___y_3492_: *mut crate::leanh::LeanObject,
    mut v___y_3493_: *mut crate::leanh::LeanObject,
    mut v___y_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3498_ =
        l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(
            v_stx_3486_,
            v_output_3487_,
            v_x_3488_,
            v___y_3489_,
            v___y_3490_,
            v___y_3491_,
            v___y_3492_,
            v___y_3493_,
            v___y_3494_,
            v___y_3495_,
            v___y_3496_,
        );
    crate::leanh::lean_dec(v___y_3496_);
    crate::leanh::lean_dec_ref(v___y_3495_);
    crate::leanh::lean_dec(v___y_3494_);
    crate::leanh::lean_dec_ref(v___y_3493_);
    crate::leanh::lean_dec(v___y_3492_);
    crate::leanh::lean_dec_ref(v___y_3491_);
    crate::leanh::lean_dec(v___y_3490_);
    crate::leanh::lean_dec_ref(v___y_3489_);
    return v_res_3498_;
}
pub unsafe fn l_Lean_Elab_Tactic_evalMatch(
    mut v_stx_3512_: *mut crate::leanh::LeanObject,
    mut v_a_3513_: *mut crate::leanh::LeanObject,
    mut v_a_3514_: *mut crate::leanh::LeanObject,
    mut v_a_3515_: *mut crate::leanh::LeanObject,
    mut v_a_3516_: *mut crate::leanh::LeanObject,
    mut v_a_3517_: *mut crate::leanh::LeanObject,
    mut v_a_3518_: *mut crate::leanh::LeanObject,
    mut v_a_3519_: *mut crate::leanh::LeanObject,
    mut v_a_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3531_: u8 = 0;
    let mut v_ref_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: u8 = 0;
    let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3554_: u8 = 0;
    let mut v_a_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3558_: u8 = 0;
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3522_ = l_Lean_Elab_Tactic_getMainTag___redArg(
                    v_a_3514_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_,
                );
                if crate::leanh::lean_obj_tag(v___x_3522_) == 0 {
                    v_a_3523_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                    crate::leanh::lean_inc(v_a_3523_);
                    crate::leanh::lean_dec_ref_known(v___x_3522_, 1);
                    crate::leanh::lean_inc(v_stx_3512_);
                    v___x_3524_ = crate::leanh::lean_alloc_closure(l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm___boxed as *mut core::ffi::c_void, 4, 2);
                    crate::leanh::lean_closure_set(v___x_3524_, 0, v_a_3523_);
                    crate::leanh::lean_closure_set(v___x_3524_, 1, v_stx_3512_);
                    v___x_3525_ =
                        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(
                            v___x_3524_,
                            v_a_3513_,
                            v_a_3514_,
                            v_a_3515_,
                            v_a_3516_,
                            v_a_3517_,
                            v_a_3518_,
                            v_a_3519_,
                            v_a_3520_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_3525_) == 0 {
                        v_a_3526_ = crate::leanh::lean_ctor_get(v___x_3525_, 0);
                        crate::leanh::lean_inc(v_a_3526_);
                        crate::leanh::lean_dec_ref_known(v___x_3525_, 1);
                        v_fst_3527_ = crate::leanh::lean_ctor_get(v_a_3526_, 0);
                        v_snd_3528_ = crate::leanh::lean_ctor_get(v_a_3526_, 1);
                        v_isSharedCheck_3554_ = (!crate::leanh::lean_is_exclusive(v_a_3526_)) as u8;
                        if v_isSharedCheck_3554_ == 0 {
                            v___x_3530_ = v_a_3526_;
                            v_isShared_3531_ = v_isSharedCheck_3554_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3528_);
                            crate::leanh::lean_inc(v_fst_3527_);
                            crate::leanh::lean_dec(v_a_3526_);
                            v___x_3530_ = crate::leanh::lean_box(0);
                            v_isShared_3531_ = v_isSharedCheck_3554_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_stx_3512_);
                        v_a_3555_ = crate::leanh::lean_ctor_get(v___x_3525_, 0);
                        v_isSharedCheck_3562_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3525_)) as u8;
                        if v_isSharedCheck_3562_ == 0 {
                            v___x_3557_ = v___x_3525_;
                            v_isShared_3558_ = v_isSharedCheck_3562_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3555_);
                            crate::leanh::lean_dec(v___x_3525_);
                            v___x_3557_ = crate::leanh::lean_box(0);
                            v_isShared_3558_ = v_isSharedCheck_3562_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_3512_);
                    v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3522_, 0);
                    v_isSharedCheck_3570_ = (!crate::leanh::lean_is_exclusive(v___x_3522_)) as u8;
                    if v_isSharedCheck_3570_ == 0 {
                        v___x_3565_ = v___x_3522_;
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3563_);
                        crate::leanh::lean_dec(v___x_3522_);
                        v___x_3565_ = crate::leanh::lean_box(0);
                        v_isShared_3566_ = v_isSharedCheck_3570_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_3532_ = crate::leanh::lean_ctor_get(v_a_3519_, 5);
                v___x_3533_ = 0;
                v___x_3534_ = l_Lean_SourceInfo_fromRef(v_ref_3532_, v___x_3533_);
                v___x_3535_ = l_Lean_Elab_Tactic_evalMatch___closed__0;
                v___x_3536_ = l_Lean_Elab_Tactic_evalMatch___closed__1;
                crate::leanh::lean_inc(v___x_3534_);
                if v_isShared_3531_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3530_, 2);
                    crate::leanh::lean_ctor_set(v___x_3530_, 1, v___x_3535_);
                    crate::leanh::lean_ctor_set(v___x_3530_, 0, v___x_3534_);
                    v___x_3538_ = v___x_3530_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3553_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3534_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3553_, 1, v___x_3535_);
                    v___x_3538_ = v_reuseFailAlloc_3553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3539_ = l_Lean_Elab_Tactic_evalMatch___closed__3;
                v___x_3540_ = l_Lean_Elab_Tactic_evalMatch___closed__4;
                crate::leanh::lean_inc_n(v___x_3534_, 2);
                v___x_3541_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3541_, 0, v___x_3534_);
                crate::leanh::lean_ctor_set(v___x_3541_, 1, v___x_3540_);
                v___x_3542_ =
                    l_Lean_Syntax_node2(v___x_3534_, v___x_3539_, v___x_3541_, v_fst_3527_);
                v___x_3543_ =
                    l_Lean_Syntax_node2(v___x_3534_, v___x_3536_, v___x_3538_, v___x_3542_);
                v___x_3544_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3545_ = lean_mk_empty_array_with_capacity(v___x_3544_);
                v___x_3546_ = lean_array_push(v___x_3545_, v___x_3543_);
                v___x_3547_ = l_Array_append___redArg(v___x_3546_, v_snd_3528_);
                crate::leanh::lean_dec(v_snd_3528_);
                v___x_3548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_mkAuxiliaryMatchTerm_spec__0___closed__4;
                v___x_3549_ = crate::leanh::lean_box(2);
                v___x_3550_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3549_);
                crate::leanh::lean_ctor_set(v___x_3550_, 1, v___x_3548_);
                crate::leanh::lean_ctor_set(v___x_3550_, 2, v___x_3547_);
                crate::leanh::lean_inc_ref(v___x_3550_);
                crate::leanh::lean_inc(v_stx_3512_);
                v___f_3551_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_Tactic_evalMatch___lam__0___boxed as *mut core::ffi::c_void,
                    11,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_3551_, 0, v_stx_3512_);
                crate::leanh::lean_closure_set(v___f_3551_, 1, v___x_3550_);
                v___x_3552_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(v_stx_3512_, v___x_3550_, v___f_3551_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
                return v___x_3552_;
            }
            3 => {
                if v_isShared_3558_ == 0 {
                    v___x_3560_ = v___x_3557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
                    v___x_3560_ = v_reuseFailAlloc_3561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3560_;
            }
            5 => {
                if v_isShared_3566_ == 0 {
                    v___x_3568_ = v___x_3565_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_evalMatch___boxed(
    mut v_stx_3571_: *mut crate::leanh::LeanObject,
    mut v_a_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3581_ = l_Lean_Elab_Tactic_evalMatch(
        v_stx_3571_,
        v_a_3572_,
        v_a_3573_,
        v_a_3574_,
        v_a_3575_,
        v_a_3576_,
        v_a_3577_,
        v_a_3578_,
        v_a_3579_,
    );
    crate::leanh::lean_dec(v_a_3579_);
    crate::leanh::lean_dec_ref(v_a_3578_);
    crate::leanh::lean_dec(v_a_3577_);
    crate::leanh::lean_dec_ref(v_a_3576_);
    crate::leanh::lean_dec(v_a_3575_);
    crate::leanh::lean_dec_ref(v_a_3574_);
    crate::leanh::lean_dec(v_a_3573_);
    crate::leanh::lean_dec_ref(v_a_3572_);
    return v_res_3581_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1(
    mut v_00_u03b1_3582_: *mut crate::leanh::LeanObject,
    mut v_x_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
    mut v___y_3585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3586_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___redArg(v_x_3583_, v___y_3585_);
    return v___x_3586_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1___boxed(
    mut v_00_u03b1_3587_: *mut crate::leanh::LeanObject,
    mut v_x_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3591_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__1(v_00_u03b1_3587_, v_x_3588_, v___y_3589_, v___y_3590_);
    crate::leanh::lean_dec_ref(v___y_3589_);
    crate::leanh::lean_dec_ref(v_x_3588_);
    return v_res_3591_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6(
    mut v_00_u03b1_3592_: *mut crate::leanh::LeanObject,
    mut v_ref_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
    mut v___y_3596_: *mut crate::leanh::LeanObject,
    mut v___y_3597_: *mut crate::leanh::LeanObject,
    mut v___y_3598_: *mut crate::leanh::LeanObject,
    mut v___y_3599_: *mut crate::leanh::LeanObject,
    mut v___y_3600_: *mut crate::leanh::LeanObject,
    mut v___y_3601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___redArg(v_ref_3593_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6___boxed(
    mut v_00_u03b1_3604_: *mut crate::leanh::LeanObject,
    mut v_ref_3605_: *mut crate::leanh::LeanObject,
    mut v___y_3606_: *mut crate::leanh::LeanObject,
    mut v___y_3607_: *mut crate::leanh::LeanObject,
    mut v___y_3608_: *mut crate::leanh::LeanObject,
    mut v___y_3609_: *mut crate::leanh::LeanObject,
    mut v___y_3610_: *mut crate::leanh::LeanObject,
    mut v___y_3611_: *mut crate::leanh::LeanObject,
    mut v___y_3612_: *mut crate::leanh::LeanObject,
    mut v___y_3613_: *mut crate::leanh::LeanObject,
    mut v___y_3614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3615_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__6(v_00_u03b1_3604_, v_ref_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
    crate::leanh::lean_dec(v___y_3613_);
    crate::leanh::lean_dec_ref(v___y_3612_);
    crate::leanh::lean_dec(v___y_3611_);
    crate::leanh::lean_dec_ref(v___y_3610_);
    crate::leanh::lean_dec(v___y_3609_);
    crate::leanh::lean_dec_ref(v___y_3608_);
    crate::leanh::lean_dec(v___y_3607_);
    crate::leanh::lean_dec_ref(v___y_3606_);
    return v_res_3615_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7(
    mut v_00_u03b1_3616_: *mut crate::leanh::LeanObject,
    mut v___y_3617_: *mut crate::leanh::LeanObject,
    mut v___y_3618_: *mut crate::leanh::LeanObject,
    mut v___y_3619_: *mut crate::leanh::LeanObject,
    mut v___y_3620_: *mut crate::leanh::LeanObject,
    mut v___y_3621_: *mut crate::leanh::LeanObject,
    mut v___y_3622_: *mut crate::leanh::LeanObject,
    mut v___y_3623_: *mut crate::leanh::LeanObject,
    mut v___y_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___redArg();
    return v___x_3626_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7___boxed(
    mut v_00_u03b1_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
    mut v___y_3633_: *mut crate::leanh::LeanObject,
    mut v___y_3634_: *mut crate::leanh::LeanObject,
    mut v___y_3635_: *mut crate::leanh::LeanObject,
    mut v___y_3636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3637_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__7(v_00_u03b1_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
    crate::leanh::lean_dec(v___y_3635_);
    crate::leanh::lean_dec_ref(v___y_3634_);
    crate::leanh::lean_dec(v___y_3633_);
    crate::leanh::lean_dec_ref(v___y_3632_);
    crate::leanh::lean_dec(v___y_3631_);
    crate::leanh::lean_dec_ref(v___y_3630_);
    crate::leanh::lean_dec(v___y_3629_);
    crate::leanh::lean_dec_ref(v___y_3628_);
    return v_res_3637_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0(
    mut v_00_u03b1_3638_: *mut crate::leanh::LeanObject,
    mut v_x_3639_: *mut crate::leanh::LeanObject,
    mut v___y_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v___y_3647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3649_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___redArg(
        v_x_3639_,
        v___y_3640_,
        v___y_3641_,
        v___y_3642_,
        v___y_3643_,
        v___y_3644_,
        v___y_3645_,
        v___y_3646_,
        v___y_3647_,
    );
    return v___x_3649_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0___boxed(
    mut v_00_u03b1_3650_: *mut crate::leanh::LeanObject,
    mut v_x_3651_: *mut crate::leanh::LeanObject,
    mut v___y_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3661_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0(
        v_00_u03b1_3650_,
        v_x_3651_,
        v___y_3652_,
        v___y_3653_,
        v___y_3654_,
        v___y_3655_,
        v___y_3656_,
        v___y_3657_,
        v___y_3658_,
        v___y_3659_,
    );
    crate::leanh::lean_dec(v___y_3659_);
    crate::leanh::lean_dec_ref(v___y_3658_);
    crate::leanh::lean_dec(v___y_3657_);
    crate::leanh::lean_dec_ref(v___y_3656_);
    crate::leanh::lean_dec(v___y_3655_);
    crate::leanh::lean_dec_ref(v___y_3654_);
    crate::leanh::lean_dec(v___y_3653_);
    crate::leanh::lean_dec_ref(v___y_3652_);
    return v_res_3661_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1(
    mut v_00_u03b1_3662_: *mut crate::leanh::LeanObject,
    mut v_stx_3663_: *mut crate::leanh::LeanObject,
    mut v_output_3664_: *mut crate::leanh::LeanObject,
    mut v_x_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3675_ =
        l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___redArg(
            v_stx_3663_,
            v_output_3664_,
            v_x_3665_,
            v___y_3666_,
            v___y_3667_,
            v___y_3668_,
            v___y_3669_,
            v___y_3670_,
            v___y_3671_,
            v___y_3672_,
            v___y_3673_,
        );
    return v___x_3675_;
}
pub unsafe fn l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1___boxed(
    mut v_00_u03b1_3676_: *mut crate::leanh::LeanObject,
    mut v_stx_3677_: *mut crate::leanh::LeanObject,
    mut v_output_3678_: *mut crate::leanh::LeanObject,
    mut v_x_3679_: *mut crate::leanh::LeanObject,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3689_ = l_Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1(
        v_00_u03b1_3676_,
        v_stx_3677_,
        v_output_3678_,
        v_x_3679_,
        v___y_3680_,
        v___y_3681_,
        v___y_3682_,
        v___y_3683_,
        v___y_3684_,
        v___y_3685_,
        v___y_3686_,
        v___y_3687_,
    );
    crate::leanh::lean_dec(v___y_3687_);
    crate::leanh::lean_dec_ref(v___y_3686_);
    crate::leanh::lean_dec(v___y_3685_);
    crate::leanh::lean_dec_ref(v___y_3684_);
    crate::leanh::lean_dec(v___y_3683_);
    crate::leanh::lean_dec_ref(v___y_3682_);
    crate::leanh::lean_dec(v___y_3681_);
    crate::leanh::lean_dec_ref(v___y_3680_);
    return v_res_3689_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0(
    mut v_cls_3690_: *mut crate::leanh::LeanObject,
    mut v_msg_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
    mut v___y_3696_: *mut crate::leanh::LeanObject,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
    mut v___y_3698_: *mut crate::leanh::LeanObject,
    mut v___y_3699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3701_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___redArg(v_cls_3690_, v_msg_3691_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
    return v___x_3701_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0___boxed(
    mut v_cls_3702_: *mut crate::leanh::LeanObject,
    mut v_msg_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
    mut v___y_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
    mut v___y_3710_: *mut crate::leanh::LeanObject,
    mut v___y_3711_: *mut crate::leanh::LeanObject,
    mut v___y_3712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3713_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__0(v_cls_3702_, v_msg_3703_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
    crate::leanh::lean_dec(v___y_3711_);
    crate::leanh::lean_dec_ref(v___y_3710_);
    crate::leanh::lean_dec(v___y_3709_);
    crate::leanh::lean_dec_ref(v___y_3708_);
    crate::leanh::lean_dec(v___y_3707_);
    crate::leanh::lean_dec_ref(v___y_3706_);
    crate::leanh::lean_dec(v___y_3705_);
    crate::leanh::lean_dec_ref(v___y_3704_);
    return v_res_3713_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3(
    mut v_as_3714_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3715_: *mut crate::leanh::LeanObject,
    mut v_b_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
    mut v___y_3721_: *mut crate::leanh::LeanObject,
    mut v___y_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3727_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___redArg(v_as_x27_3715_, v_b_3716_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
    return v___x_3727_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3___boxed(
    mut v_as_3728_: *mut crate::leanh::LeanObject,
    mut v_as_x27_3729_: *mut crate::leanh::LeanObject,
    mut v_b_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
    mut v___y_3734_: *mut crate::leanh::LeanObject,
    mut v___y_3735_: *mut crate::leanh::LeanObject,
    mut v___y_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__3(v_as_3728_, v_as_x27_3729_, v_b_3730_, v_a_3731_, v___y_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_, v___y_3739_);
    crate::leanh::lean_dec(v___y_3739_);
    crate::leanh::lean_dec_ref(v___y_3738_);
    crate::leanh::lean_dec(v___y_3737_);
    crate::leanh::lean_dec_ref(v___y_3736_);
    crate::leanh::lean_dec(v___y_3735_);
    crate::leanh::lean_dec_ref(v___y_3734_);
    crate::leanh::lean_dec(v___y_3733_);
    crate::leanh::lean_dec_ref(v___y_3732_);
    crate::leanh::lean_dec(v_as_x27_3729_);
    crate::leanh::lean_dec(v_as_3728_);
    return v_res_3741_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5(
    mut v_00_u03b1_3742_: *mut crate::leanh::LeanObject,
    mut v_ref_3743_: *mut crate::leanh::LeanObject,
    mut v_msg_3744_: *mut crate::leanh::LeanObject,
    mut v___y_3745_: *mut crate::leanh::LeanObject,
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
    mut v___y_3748_: *mut crate::leanh::LeanObject,
    mut v___y_3749_: *mut crate::leanh::LeanObject,
    mut v___y_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___redArg(v_ref_3743_, v_msg_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
    return v___x_3754_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5___boxed(
    mut v_00_u03b1_3755_: *mut crate::leanh::LeanObject,
    mut v_ref_3756_: *mut crate::leanh::LeanObject,
    mut v_msg_3757_: *mut crate::leanh::LeanObject,
    mut v___y_3758_: *mut crate::leanh::LeanObject,
    mut v___y_3759_: *mut crate::leanh::LeanObject,
    mut v___y_3760_: *mut crate::leanh::LeanObject,
    mut v___y_3761_: *mut crate::leanh::LeanObject,
    mut v___y_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
    mut v___y_3765_: *mut crate::leanh::LeanObject,
    mut v___y_3766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3767_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5(v_00_u03b1_3755_, v_ref_3756_, v_msg_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_, v___y_3762_, v___y_3763_, v___y_3764_, v___y_3765_);
    crate::leanh::lean_dec(v___y_3765_);
    crate::leanh::lean_dec_ref(v___y_3764_);
    crate::leanh::lean_dec(v___y_3763_);
    crate::leanh::lean_dec_ref(v___y_3762_);
    crate::leanh::lean_dec(v___y_3761_);
    crate::leanh::lean_dec_ref(v___y_3760_);
    crate::leanh::lean_dec(v___y_3759_);
    crate::leanh::lean_dec_ref(v___y_3758_);
    crate::leanh::lean_dec(v_ref_3756_);
    return v_res_3767_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15(
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
    mut v___y_3771_: *mut crate::leanh::LeanObject,
    mut v___y_3772_: *mut crate::leanh::LeanObject,
    mut v___y_3773_: *mut crate::leanh::LeanObject,
    mut v___y_3774_: *mut crate::leanh::LeanObject,
    mut v___y_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3777_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___redArg(v___y_3775_);
    return v___x_3777_;
}
pub unsafe fn l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15___boxed(
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
    mut v___y_3784_: *mut crate::leanh::LeanObject,
    mut v___y_3785_: *mut crate::leanh::LeanObject,
    mut v___y_3786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3787_ = l_Lean_Elab_getResetInfoTrees___at___00Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9_spec__15(v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
    crate::leanh::lean_dec(v___y_3785_);
    crate::leanh::lean_dec_ref(v___y_3784_);
    crate::leanh::lean_dec(v___y_3783_);
    crate::leanh::lean_dec_ref(v___y_3782_);
    crate::leanh::lean_dec(v___y_3781_);
    crate::leanh::lean_dec_ref(v___y_3780_);
    crate::leanh::lean_dec(v___y_3779_);
    crate::leanh::lean_dec_ref(v___y_3778_);
    return v_res_3787_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9(
    mut v_00_u03b1_3788_: *mut crate::leanh::LeanObject,
    mut v_x_3789_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_3790_: *mut crate::leanh::LeanObject,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
    mut v___y_3797_: *mut crate::leanh::LeanObject,
    mut v___y_3798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3800_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___redArg(v_x_3789_, v_mkInfoTree_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
    return v___x_3800_;
}
pub unsafe fn l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9___boxed(
    mut v_00_u03b1_3801_: *mut crate::leanh::LeanObject,
    mut v_x_3802_: *mut crate::leanh::LeanObject,
    mut v_mkInfoTree_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
    mut v___y_3805_: *mut crate::leanh::LeanObject,
    mut v___y_3806_: *mut crate::leanh::LeanObject,
    mut v___y_3807_: *mut crate::leanh::LeanObject,
    mut v___y_3808_: *mut crate::leanh::LeanObject,
    mut v___y_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3813_ = l_Lean_Elab_withInfoTreeContext___at___00Lean_Elab_withMacroExpansionInfo___at___00Lean_Elab_Tactic_evalMatch_spec__1_spec__9(v_00_u03b1_3801_, v_x_3802_, v_mkInfoTree_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_, v___y_3808_, v___y_3809_, v___y_3810_, v___y_3811_);
    crate::leanh::lean_dec(v___y_3811_);
    crate::leanh::lean_dec_ref(v___y_3810_);
    crate::leanh::lean_dec(v___y_3809_);
    crate::leanh::lean_dec_ref(v___y_3808_);
    crate::leanh::lean_dec(v___y_3807_);
    crate::leanh::lean_dec_ref(v___y_3806_);
    crate::leanh::lean_dec(v___y_3805_);
    crate::leanh::lean_dec_ref(v___y_3804_);
    return v_res_3813_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6(
    mut v_00_u03b2_3814_: *mut crate::leanh::LeanObject,
    mut v_m_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3817_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___redArg(v_m_3815_, v_a_3816_);
    return v___x_3817_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_3818_: *mut crate::leanh::LeanObject,
    mut v_m_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6(v_00_u03b2_3818_, v_m_3819_, v_a_3820_);
    crate::leanh::lean_dec(v_a_3820_);
    crate::leanh::lean_dec_ref(v_m_3819_);
    return v_res_3821_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10(
    mut v_00_u03b1_3822_: *mut crate::leanh::LeanObject,
    mut v_msg_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
    mut v___y_3827_: *mut crate::leanh::LeanObject,
    mut v___y_3828_: *mut crate::leanh::LeanObject,
    mut v___y_3829_: *mut crate::leanh::LeanObject,
    mut v___y_3830_: *mut crate::leanh::LeanObject,
    mut v___y_3831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___redArg(v_msg_3823_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_);
    return v___x_3833_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10___boxed(
    mut v_00_u03b1_3834_: *mut crate::leanh::LeanObject,
    mut v_msg_3835_: *mut crate::leanh::LeanObject,
    mut v___y_3836_: *mut crate::leanh::LeanObject,
    mut v___y_3837_: *mut crate::leanh::LeanObject,
    mut v___y_3838_: *mut crate::leanh::LeanObject,
    mut v___y_3839_: *mut crate::leanh::LeanObject,
    mut v___y_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
    mut v___y_3844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3845_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__5_spec__10(v_00_u03b1_3834_, v_msg_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
    crate::leanh::lean_dec(v___y_3843_);
    crate::leanh::lean_dec_ref(v___y_3842_);
    crate::leanh::lean_dec(v___y_3841_);
    crate::leanh::lean_dec_ref(v___y_3840_);
    crate::leanh::lean_dec(v___y_3839_);
    crate::leanh::lean_dec_ref(v___y_3838_);
    crate::leanh::lean_dec(v___y_3837_);
    crate::leanh::lean_dec_ref(v___y_3836_);
    return v_res_3845_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8(
    mut v_00_u03b2_3846_: *mut crate::leanh::LeanObject,
    mut v_x_3847_: *mut crate::leanh::LeanObject,
    mut v_x_3848_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3849_: u8 = 0;
    v___x_3849_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___redArg(v_x_3847_, v_x_3848_);
    return v___x_3849_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_3850_: *mut crate::leanh::LeanObject,
    mut v_x_3851_: *mut crate::leanh::LeanObject,
    mut v_x_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3853_: u8 = 0;
    let mut v_r_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8(v_00_u03b2_3850_, v_x_3851_, v_x_3852_);
    crate::leanh::lean_dec_ref(v_x_3852_);
    crate::leanh::lean_dec_ref(v_x_3851_);
    v_r_3854_ = crate::leanh::lean_box((v_res_3853_) as usize);
    return v_r_3854_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11(
    mut v_00_u03b2_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_x_3857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___redArg(v_a_3856_, v_x_3857_);
    return v___x_3858_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11___boxed(
    mut v_00_u03b2_3859_: *mut crate::leanh::LeanObject,
    mut v_a_3860_: *mut crate::leanh::LeanObject,
    mut v_x_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3862_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__6_spec__11(v_00_u03b2_3859_, v_a_3860_, v_x_3861_);
    crate::leanh::lean_dec(v_x_3861_);
    crate::leanh::lean_dec(v_a_3860_);
    return v_res_3862_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14(
    mut v_00_u03b2_3863_: *mut crate::leanh::LeanObject,
    mut v_x_3864_: *mut crate::leanh::LeanObject,
    mut v_x_3865_: usize,
    mut v_x_3866_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3867_: u8 = 0;
    v___x_3867_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___redArg(v_x_3864_, v_x_3865_, v_x_3866_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14___boxed(
    mut v_00_u03b2_3868_: *mut crate::leanh::LeanObject,
    mut v_x_3869_: *mut crate::leanh::LeanObject,
    mut v_x_3870_: *mut crate::leanh::LeanObject,
    mut v_x_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26487__boxed_3872_: usize = 0;
    let mut v_res_3873_: u8 = 0;
    let mut v_r_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26487__boxed_3872_ = crate::leanh::lean_unbox_usize(v_x_3870_);
    crate::leanh::lean_dec(v_x_3870_);
    v_res_3873_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14(v_00_u03b2_3868_, v_x_3869_, v_x_26487__boxed_3872_, v_x_3871_);
    crate::leanh::lean_dec_ref(v_x_3871_);
    crate::leanh::lean_dec_ref(v_x_3869_);
    v_r_3874_ = crate::leanh::lean_box((v_res_3873_) as usize);
    return v_r_3874_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18(
    mut v_00_u03b2_3875_: *mut crate::leanh::LeanObject,
    mut v_keys_3876_: *mut crate::leanh::LeanObject,
    mut v_vals_3877_: *mut crate::leanh::LeanObject,
    mut v_heq_3878_: *mut crate::leanh::LeanObject,
    mut v_i_3879_: *mut crate::leanh::LeanObject,
    mut v_k_3880_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3881_: u8 = 0;
    v___x_3881_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___redArg(v_keys_3876_, v_i_3879_, v_k_3880_);
    return v___x_3881_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18___boxed(
    mut v_00_u03b2_3882_: *mut crate::leanh::LeanObject,
    mut v_keys_3883_: *mut crate::leanh::LeanObject,
    mut v_vals_3884_: *mut crate::leanh::LeanObject,
    mut v_heq_3885_: *mut crate::leanh::LeanObject,
    mut v_i_3886_: *mut crate::leanh::LeanObject,
    mut v_k_3887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3888_: u8 = 0;
    let mut v_r_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3888_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Tactic_evalMatch_spec__0_spec__2_spec__4_spec__8_spec__14_spec__18(v_00_u03b2_3882_, v_keys_3883_, v_vals_3884_, v_heq_3885_, v_i_3886_, v_k_3887_);
    crate::leanh::lean_dec_ref(v_k_3887_);
    crate::leanh::lean_dec_ref(v_vals_3884_);
    crate::leanh::lean_dec_ref(v_keys_3883_);
    v_r_3889_ = crate::leanh::lean_box((v_res_3888_) as usize);
    return v_r_3889_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3903_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3904_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__0;
    v___x_3905_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3;
    v___x_3906_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Tactic_evalMatch___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3907_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3903_,
        v___x_3904_,
        v___x_3905_,
        v___x_3906_,
    );
    return v___x_3907_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___boxed(
    mut v_a_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3909_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1();
    return v_res_3909_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3936_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1___closed__3;
    v___x_3937_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___closed__6;
    v___x_3938_ = l_Lean_addBuiltinDeclarationRanges(v___x_3936_, v___x_3937_);
    return v___x_3938_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3___boxed(
    mut v_a_3939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3940_ = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3();
    return v_res_3940_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Match(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Match_0__Lean_Elab_Tactic_evalMatch___regBuiltin_Lean_Elab_Tactic_evalMatch_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Match(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Match(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Induction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Match(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Match(builtin);
}
