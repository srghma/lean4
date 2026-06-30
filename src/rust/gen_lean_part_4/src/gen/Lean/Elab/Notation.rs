// Lean compiler output
// Module: Lean.Elab.Notation
// Imports: Lean.Elab.Syntax Lean.Elab.AuxDef Lean.Elab.BuiltinNotation
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_dec_eq, lean_uint64_of_nat, lean_uint64_shift_right,
    lean_uint64_to_usize, lean_uint64_xor, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt,
    lean_usize_land, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_TSepArray_getElems___redArg,
    l_Lean_Syntax_getTailInfo, l_Lean_Syntax_isNone, l_Lean_Syntax_mkApp, l_Lean_Syntax_mkNumLit,
    l_Lean_Syntax_setHeadInfo, l_Lean_Syntax_setTailInfo, l_Lean_TSyntax_getHygieneInfo,
    l_Lean_TSyntax_getId, l_Lean_evalOptPrio___boxed, l_Lean_mkIdentFrom, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Lean_Macro_resolveGlobalName,
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getHeadInfo, l_Lean_Syntax_getId,
    l_Lean_Syntax_getKind, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1,
    l_Lean_Syntax_node2, l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5,
    l_Lean_Syntax_node6, l_Lean_addMacroScope, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
    l_String_toRawSubstring_x27, lean_erase_macro_scopes,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_isAnonymous, l_Lean_Name_isPrefixOf};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Elab::AuxDef::{
    initialize_Lean_Elab_AuxDef, runtime_initialize_Lean_Elab_AuxDef,
};
use crate::r#gen::Lean::Elab::BuiltinNotation::{
    initialize_Lean_Elab_BuiltinNotation, l_Lean_Elab_Term_expandCDot_x3f,
    runtime_initialize_Lean_Elab_BuiltinNotation,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_elabCommand,
    l_Lean_Elab_Command_elabCommand___boxed, l_Lean_Elab_Command_getCurrMacroScope___redArg,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Elab_Command_withScope___redArg, l_Lean_Parser_Command_visibility_ofAttrKind,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::Quotation::Precheck::l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
use crate::r#gen::Lean::Elab::Syntax::{
    initialize_Lean_Elab_Syntax, l_Lean_Elab_Command_elabSyntax,
    l_Lean_Elab_Command_isLocalAttrKind, l_Lean_Elab_Command_strLitToPattern___redArg,
    runtime_initialize_Lean_Elab_Syntax,
};
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
use crate::r#gen::Lean::Syntax::{
    l_Lean_Syntax_getAntiquotTerm, l_Lean_Syntax_isAntiquot, l_Lean_Syntax_mkAntiquotNode,
    l_Lean_Syntax_topDown,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
pub static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value
        ) as *mut leanh::LeanObject,
        5117844058249666356 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value:
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
    m_data: [116, 101, 114, 109, 0],
};
static mut l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value
) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2_value
        ) as *mut leanh::LeanObject,
        8609355255726335675 as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [97, 116, 116, 114, 73, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__3_value) as *mut leanh::LeanObject,7499624980761693169 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [97, 116, 116, 114, 75, 105, 110, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__5_value) as *mut leanh::LeanObject,7983999284776576032 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [65, 116, 116, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__7_value) as *mut leanh::LeanObject,4584992172905639687 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__8_value) as *mut leanh::LeanObject,3878072352281346923 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [105, 110, 104, 101, 114, 105, 116, 95, 100, 111, 99, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__10_value) as *mut leanh::LeanObject,11976168950125103187 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 117, 108, 108, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__12_value) as *mut leanh::LeanObject,9855511589286918680 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_addInheritDocDefault___closed__0_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_addInheritDocDefault___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_addInheritDocDefault___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__0_value)
            as *mut leanh::LeanObject,
        12966880221525079621 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_addInheritDocDefault___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_addInheritDocDefault___closed__2_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_addInheritDocDefault___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_addInheritDocDefault___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value:
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
    m_data: [83, 121, 110, 116, 97, 120, 0],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [99, 97, 116, 0],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_2:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value)
            as *mut leanh::LeanObject,
        1765827125244227832 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__1_value)
            as *mut leanh::LeanObject,
        14125453249386077023 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__4_value)
            as *mut leanh::LeanObject,
        11586196343691998021 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 100, 101, 110, 116, 80, 114, 101, 99, 0],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_2:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value)
            as *mut leanh::LeanObject,
        17342580262104060118 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__9_value)
            as *mut leanh::LeanObject,
        9101404829963262459 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__11_value)
            as *mut leanh::LeanObject,
        9232979286016572671 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [117, 110, 105, 99, 111, 100, 101, 65, 116, 111, 109, 0],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_2:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value)
            as *mut leanh::LeanObject,
        1765827125244227832 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__13_value)
            as *mut leanh::LeanObject,
        7882745399186723613 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value:
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
    m_data: [97, 116, 111, 109, 0],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value)
            as *mut leanh::LeanObject,
        1765827125244227832 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value:
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
            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__15_value)
            as *mut leanh::LeanObject,
        6376237424612349584 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_removeParentheses___closed__0_value: leanh::LeanStringObject<
    6,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_removeParentheses___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_removeParentheses___closed__1_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__1_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__0_value)
            as *mut leanh::LeanObject,
        7932075773091973500 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_removeParentheses___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_removeParentheses___closed__2_value: leanh::LeanStringObject<
    15,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_removeParentheses___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_removeParentheses___closed__3_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__3_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__2_value)
            as *mut leanh::LeanObject,
        7306243862518720553 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_removeParentheses___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_removeParentheses___closed__4_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_removeParentheses___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_removeParentheses___closed__5_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__4_value)
            as *mut leanh::LeanObject,
        9871775667037945883 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_removeParentheses___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_removeParentheses___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__0_value) as *mut leanh::LeanObject,11985596712582660667 as *mut leanh::LeanObject] };
static mut l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__1_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(
                l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0_value
            ) as *mut leanh::LeanObject,
            5117844058249666356 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkUnexpander___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__1_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__0_value)
                as *mut leanh::LeanObject,
            11311673461297540074 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__2_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [36, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__3_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [102, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__3_value)
                as *mut leanh::LeanObject,
            1707590486618227741 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__6_value: leanh::LeanStringObject<13> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [97, 110, 116, 105, 113, 117, 111, 116, 78, 97, 109, 101, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__6_value)
                as *mut leanh::LeanObject,
            5763156871072657475 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__8_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__9_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__8_value)
                as *mut leanh::LeanObject,
            11510100434945111860 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            16981400742628996529 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkUnexpander___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__10_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__9_value)
                as *mut leanh::LeanObject,
            6797826372810318163 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__11_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__11_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__12_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__12_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__11_value)
                as *mut leanh::LeanObject,
            2533412339571800130 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__13_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__14_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            97, 112, 112, 95, 117, 110, 101, 120, 112, 97, 110, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__16_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__14_value)
                as *mut leanh::LeanObject,
            1464131427232734893 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__16_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__17_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__17: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__17_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__18_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [117, 110, 101, 120, 112, 97, 110, 100, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__20_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__18_value)
                as *mut leanh::LeanObject,
            5532461465038330410 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__20_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__21_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 30,
        m_capacity: 30,
        m_length: 29,
        m_data: [
            76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114,
            46, 85, 110, 101, 120, 112, 97, 110, 100, 101, 114, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__21: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__21_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__23_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 0,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__23: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__23_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__24_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [85, 110, 101, 120, 112, 97, 110, 100, 101, 114, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__24: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__24_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__23_value)
                as *mut leanh::LeanObject,
            300274991653824376 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkUnexpander___closed__25_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__25_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__24_value)
                as *mut leanh::LeanObject,
            18396238064604751231 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__25_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__26_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__26: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__26_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__27_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__27_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__28_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__28_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__27_value)
                as *mut leanh::LeanObject,
            7043493786777132025 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__28: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__28_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__29_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__29_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__30_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__30_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__29_value)
                as *mut leanh::LeanObject,
            13242179749370575553 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__30: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__30_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__31_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__31_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__32_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__32_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__31_value)
                as *mut leanh::LeanObject,
            16529391333736644786 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__32: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__32_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__33_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__33_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__34_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__34: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__34_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__35_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__35_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__34_value)
                as *mut leanh::LeanObject,
            5855146430765573009 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__35_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__36_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__36: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__36_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__37_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__37: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__37_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__38_value: leanh::LeanStringObject<3> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__38: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__38_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__39_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [119, 105, 116, 104, 82, 101, 102, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__39: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__39_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__40_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__40: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__41_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__39_value)
                as *mut leanh::LeanObject,
            13375064300761729729 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__41: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__41_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__42_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__42_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__42_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__39_value)
                as *mut leanh::LeanObject,
            17178278425789313152 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__42: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__42_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__43_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__43: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__43_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__44_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__44_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__43_value)
                as *mut leanh::LeanObject,
            3984140175429830279 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__44: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__44_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__45_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__45: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__45_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__46_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__46: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__46_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__47_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__47: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_mkUnexpander___closed__48_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__46_value)
                as *mut leanh::LeanObject,
            8214547835296698684 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__48: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__48_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__49_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__49: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__49_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__50_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__49_value)
                as *mut leanh::LeanObject,
            8171668748642392738 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkUnexpander___closed__50_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__50_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__46_value)
                as *mut leanh::LeanObject,
            3883738120033471353 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__50: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__50_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__51_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 117, 112, 108, 101, 0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__51: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__51_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__52_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__52_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__51_value)
                as *mut leanh::LeanObject,
            15644373471618144447 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__52: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__52_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__53_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_mkUnexpander___closed__53: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__53_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__54_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__54: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__54_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_mkUnexpander___closed__55_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__55: *mut leanh::LeanObject =
    core::ptr::null_mut();
static l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__8_value)
                as *mut leanh::LeanObject,
            11510100434945111860 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_mkUnexpander___closed__56_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__56_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            16981400742628996529 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__56: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__56_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__57_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__56_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__57: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__57_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__58_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__58_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__58: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__58_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__59_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__58_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__59: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__59_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__60_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__60_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2_value) as *mut leanh::LeanObject,16572064140653406795 as *mut leanh::LeanObject] };
static mut l_Lean_Elab_Command_mkUnexpander___closed__60: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__60_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__61_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__60_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__61: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__61_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_mkUnexpander___closed__62_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
pub static l_Lean_Elab_Command_mkUnexpander___closed__62_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__62_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__0_value
            ) as *mut leanh::LeanObject,
            5337926038336999469 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__62: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__62_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__63_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__62_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__63: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__63_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__64_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__63_value)
                as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__64: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__64_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__65_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__61_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__64_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__65: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__65_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__66_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__59_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__65_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__66: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__66_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__67_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__57_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__66_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__67: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__67_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_mkUnexpander___closed__68_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_Command_mkUnexpander___closed__68: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__68_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__0_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1_value) as *mut leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__1_value) as *mut leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2_value) as *mut leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject,7310567555909517314 as *mut leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__1_value) as *mut leanh::LeanObject,273128857561458264 as *mut leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__3_value) as *mut leanh::LeanObject,7870113334857981723 as *mut leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5_value: leanh::LeanStringObject<16> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18_value) as *mut leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1_value) as *mut leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value: leanh::LeanStringObject<158> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__0_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [110, 111, 116, 97, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabNotation___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__1_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__1_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabNotation___closed__1_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__1_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__0_value)
                as *mut leanh::LeanObject,
            13116756686754095629 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__2_value: leanh::LeanStringObject<12> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabNotation___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__3_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabNotation___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__3_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__2_value)
                as *mut leanh::LeanObject,
            127604530719969405 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__4_value: leanh::LeanStringObject<15> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            112, 114, 101, 99, 104, 101, 99, 107, 101, 100, 81, 117, 111, 116, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__5_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__6_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabNotation___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__7_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabNotation___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__6_value)
                as *mut leanh::LeanObject,
            13348752267415789739 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__8_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__9_value: leanh::LeanStringObject<10> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__9_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabNotation___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__10_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__10_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__10_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabNotation___closed__10_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__10_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__9_value)
                as *mut leanh::LeanObject,
            17682753938374962505 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__11_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__12_value: leanh::LeanStringObject<7> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__12_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabNotation___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__13_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__13_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabNotation___closed__13_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__13_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__12_value)
                as *mut leanh::LeanObject,
            2812521669163367463 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__13_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___closed__14_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabNotation___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__14_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabNotation___closed__15_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__15_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__15_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1_value) as *mut leanh::LeanObject,8018486133748762727 as *mut leanh::LeanObject] };
static l_Lean_Elab_Command_elabNotation___closed__15_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__15_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value
            ) as *mut leanh::LeanObject,
            17342580262104060118 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabNotation___closed__15_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__15_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__14_value)
                as *mut leanh::LeanObject,
            9063780239635860524 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabNotation___closed__15: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___closed__15_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabNotation___boxed__const__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + core::mem::size_of::<usize>() * 1) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(0 as *mut leanh::LeanObject)],
};
pub static mut l_Lean_Elab_Command_elabNotation___boxed__const__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabNotation___boxed__const__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 108, 97, 98, 78, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_mkUnexpander___closed__8_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__8_value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__0_value) as *mut leanh::LeanObject,17931042821208625495 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(
    mut v_id_3066_: *mut leanh::LeanObject,
    mut v_as_3067_: *mut leanh::LeanObject,
    mut v_i_3068_: usize,
    mut v_stop_3069_: usize,
) -> u8 {
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: u8 = 0;
    let mut v___x_3075_: usize = 0;
    let mut v___x_3076_: usize = 0;
    let mut v___x_3078_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3070_ = lean_usize_dec_eq(v_i_3068_, v_stop_3069_);
                if v___x_3070_ == 0 {
                    v___x_3071_ = lean_array_uget_borrowed(v_as_3067_, v_i_3068_);
                    v___x_3072_ = l_Lean_Syntax_getId(v___x_3071_);
                    v___x_3073_ = l_Lean_TSyntax_getId(v_id_3066_);
                    v___x_3074_ = lean_name_eq(v___x_3072_, v___x_3073_);
                    leanh::lean_dec(v___x_3073_);
                    leanh::lean_dec(v___x_3072_);
                    if v___x_3074_ == 0 {
                        v___x_3075_ = 1usize;
                        v___x_3076_ = lean_usize_add(v_i_3068_, v___x_3075_);
                        v_i_3068_ = v___x_3076_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3074_;
                    }
                } else {
                    v___x_3078_ = 0;
                    return v___x_3078_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1___boxed(
    mut v_id_3079_: *mut leanh::LeanObject,
    mut v_as_3080_: *mut leanh::LeanObject,
    mut v_i_3081_: *mut leanh::LeanObject,
    mut v_stop_3082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_3083_: usize = 0;
    let mut v_stop_boxed_3084_: usize = 0;
    let mut v_res_3085_: u8 = 0;
    let mut v_r_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3083_ = leanh::lean_unbox_usize(v_i_3081_);
    leanh::lean_dec(v_i_3081_);
    v_stop_boxed_3084_ = leanh::lean_unbox_usize(v_stop_3082_);
    leanh::lean_dec(v_stop_3082_);
    v_res_3085_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_id_3079_, v_as_3080_, v_i_boxed_3083_, v_stop_boxed_3084_);
    leanh::lean_dec_ref(v_as_3080_);
    leanh::lean_dec(v_id_3079_);
    v_r_3086_ = leanh::lean_box((v_res_3085_) as usize);
    return v_r_3086_;
}
pub unsafe fn l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(
    mut v_vars_3093_: *mut leanh::LeanObject,
    mut v_x_3094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: u8 = 0;
    let mut v_info_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v_sz_3103_: usize = 0;
    let mut v___x_3104_: usize = 0;
    let mut v___x_3105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3109_: u8 = 0;
    let mut v___x_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: u8 = 0;
    let mut v___x_3113_: usize = 0;
    let mut v___x_3114_: usize = 0;
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3095_ =
                    l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                leanh::lean_inc(v_x_3094_);
                v___x_3096_ = l_Lean_Syntax_isOfKind(v_x_3094_, v___x_3095_);
                if v___x_3096_ == 0 {
                    if leanh::lean_obj_tag(v_x_3094_) == 1 {
                        v_info_3097_ = leanh::lean_ctor_get(v_x_3094_, 0);
                        v_kind_3098_ = leanh::lean_ctor_get(v_x_3094_, 1);
                        v_args_3099_ = leanh::lean_ctor_get(v_x_3094_, 2);
                        v_isSharedCheck_3109_ = (!leanh::lean_is_exclusive(v_x_3094_)) as u8;
                        if v_isSharedCheck_3109_ == 0 {
                            v___x_3101_ = v_x_3094_;
                            v_isShared_3102_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_args_3099_);
                            leanh::lean_inc(v_kind_3098_);
                            leanh::lean_inc(v_info_3097_);
                            leanh::lean_dec(v_x_3094_);
                            v___x_3101_ = leanh::lean_box(0);
                            v_isShared_3102_ = v_isSharedCheck_3109_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v_x_3094_;
                    }
                } else {
                    v___x_3110_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3111_ = lean_array_get_size(v_vars_3093_);
                    v___x_3112_ = lean_nat_dec_lt(v___x_3110_, v___x_3111_);
                    if v___x_3112_ == 0 {
                        return v_x_3094_;
                    } else {
                        if v___x_3112_ == 0 {
                            return v_x_3094_;
                        } else {
                            v___x_3113_ = 0usize;
                            v___x_3114_ = lean_usize_of_nat(v___x_3111_);
                            v___x_3115_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__1(v_x_3094_, v_vars_3093_, v___x_3113_, v___x_3114_);
                            if v___x_3115_ == 0 {
                                return v_x_3094_;
                            } else {
                                v___x_3116_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
                                v___x_3117_ = leanh::lean_box(0);
                                v___x_3118_ = l_Lean_Syntax_mkAntiquotNode(
                                    v___x_3116_,
                                    v_x_3094_,
                                    v___x_3110_,
                                    v___x_3117_,
                                    v___x_3096_,
                                );
                                return v___x_3118_;
                            }
                        }
                    }
                }
            }
            1 => {
                v_sz_3103_ = lean_array_size(v_args_3099_);
                v___x_3104_ = 0usize;
                v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_3093_, v_sz_3103_, v___x_3104_, v_args_3099_);
                if v_isShared_3102_ == 0 {
                    leanh::lean_ctor_set(v___x_3101_, 2, v___x_3105_);
                    v___x_3107_ = v___x_3101_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3108_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_info_3097_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 1, v_kind_3098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3108_, 2, v___x_3105_);
                    v___x_3107_ = v_reuseFailAlloc_3108_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3107_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(
    mut v_vars_3119_: *mut leanh::LeanObject,
    mut v_sz_3120_: usize,
    mut v_i_3121_: usize,
    mut v_bs_3122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3123_: u8 = 0;
    let mut v_v_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: usize = 0;
    let mut v___x_3129_: usize = 0;
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3123_ = lean_usize_dec_lt(v_i_3121_, v_sz_3120_);
                if v___x_3123_ == 0 {
                    return v_bs_3122_;
                } else {
                    v_v_3124_ = lean_array_uget(v_bs_3122_, v_i_3121_);
                    v___x_3125_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3126_ = lean_array_uset(v_bs_3122_, v_i_3121_, v___x_3125_);
                    v___x_3127_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(
                        v_vars_3119_,
                        v_v_3124_,
                    );
                    v___x_3128_ = 1usize;
                    v___x_3129_ = lean_usize_add(v_i_3121_, v___x_3128_);
                    v___x_3130_ = lean_array_uset(v_bs_x27_3126_, v_i_3121_, v___x_3127_);
                    v_i_3121_ = v___x_3129_;
                    v_bs_3122_ = v___x_3130_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0___boxed(
    mut v_vars_3132_: *mut leanh::LeanObject,
    mut v_sz_3133_: *mut leanh::LeanObject,
    mut v_i_3134_: *mut leanh::LeanObject,
    mut v_bs_3135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3136_: usize = 0;
    let mut v_i_boxed_3137_: usize = 0;
    let mut v_res_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3136_ = leanh::lean_unbox_usize(v_sz_3133_);
    leanh::lean_dec(v_sz_3133_);
    v_i_boxed_3137_ = leanh::lean_unbox_usize(v_i_3134_);
    leanh::lean_dec(v_i_3134_);
    v_res_3138_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote_spec__0(v_vars_3132_, v_sz_boxed_3136_, v_i_boxed_3137_, v_bs_3135_);
    leanh::lean_dec_ref(v_vars_3132_);
    return v_res_3138_;
}
pub unsafe fn l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___boxed(
    mut v_vars_3139_: *mut leanh::LeanObject,
    mut v_x_3140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3141_ =
        l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(v_vars_3139_, v_x_3140_);
    leanh::lean_dec_ref(v_vars_3139_);
    return v_res_3141_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3170_ = l_Array_mkArray0(leanh::lean_box(0));
    return v___x_3170_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(
    mut v___x_3171_: u8,
    mut v___x_3172_: *mut leanh::LeanObject,
    mut v_sz_3173_: usize,
    mut v_i_3174_: usize,
    mut v_bs_3175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3176_: u8 = 0;
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3183_: usize = 0;
    let mut v___x_3184_: usize = 0;
    let mut v___x_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3187_: u8 = 0;
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: u8 = 0;
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: u8 = 0;
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: u8 = 0;
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: u8 = 0;
    let mut v___x_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3176_ = lean_usize_dec_lt(v_i_3174_, v_sz_3173_);
                if v___x_3176_ == 0 {
                    leanh::lean_dec(v___x_3172_);
                    return v_bs_3175_;
                } else {
                    v___x_3177_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4;
                    v_v_3178_ = lean_array_uget(v_bs_3175_, v_i_3174_);
                    v___x_3179_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3180_ = lean_array_uset(v_bs_3175_, v_i_3174_, v___x_3179_);
                    leanh::lean_inc(v_v_3178_);
                    v___x_3187_ = l_Lean_Syntax_isOfKind(v_v_3178_, v___x_3177_);
                    if v___x_3187_ == 0 {
                        v___y_3182_ = v_v_3178_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3188_ = l_Lean_Syntax_getArg(v_v_3178_, v___x_3179_);
                        v___x_3189_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6;
                        leanh::lean_inc(v___x_3188_);
                        v___x_3190_ = l_Lean_Syntax_isOfKind(v___x_3188_, v___x_3189_);
                        if v___x_3190_ == 0 {
                            leanh::lean_dec(v___x_3188_);
                            v___y_3182_ = v_v_3178_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3191_ = l_Lean_Syntax_getArg(v___x_3188_, v___x_3179_);
                            leanh::lean_dec(v___x_3188_);
                            v___x_3192_ = l_Lean_Syntax_matchesNull(v___x_3191_, v___x_3179_);
                            if v___x_3192_ == 0 {
                                v___y_3182_ = v_v_3178_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3193_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3194_ = l_Lean_Syntax_getArg(v_v_3178_, v___x_3193_);
                                v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9;
                                leanh::lean_inc(v___x_3194_);
                                v___x_3196_ = l_Lean_Syntax_isOfKind(v___x_3194_, v___x_3195_);
                                if v___x_3196_ == 0 {
                                    leanh::lean_dec(v___x_3194_);
                                    v___y_3182_ = v_v_3178_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3197_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                                    v_attr_3198_ = l_Lean_Syntax_getArg(v___x_3194_, v___x_3179_);
                                    leanh::lean_inc(v_attr_3198_);
                                    v___x_3199_ = l_Lean_Syntax_isOfKind(v_attr_3198_, v___x_3197_);
                                    if v___x_3199_ == 0 {
                                        leanh::lean_dec(v_attr_3198_);
                                        leanh::lean_dec(v___x_3194_);
                                        v___y_3182_ = v_v_3178_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3200_ =
                                            l_Lean_Syntax_getArg(v___x_3194_, v___x_3193_);
                                        leanh::lean_dec(v___x_3194_);
                                        v___x_3201_ =
                                            l_Lean_Syntax_matchesNull(v___x_3200_, v___x_3179_);
                                        if v___x_3201_ == 0 {
                                            leanh::lean_dec(v_attr_3198_);
                                            v___y_3182_ = v_v_3178_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3202_ = l_Lean_TSyntax_getId(v_attr_3198_);
                                            v___x_3203_ = lean_erase_macro_scopes(v___x_3202_);
                                            v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11;
                                            v___x_3205_ = lean_name_eq(v___x_3203_, v___x_3204_);
                                            leanh::lean_dec(v___x_3203_);
                                            if v___x_3205_ == 0 {
                                                leanh::lean_dec(v_attr_3198_);
                                                v___y_3182_ = v_v_3178_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_v_3178_);
                                                v___x_3206_ = leanh::lean_box(0);
                                                v___x_3207_ = l_Lean_SourceInfo_fromRef(
                                                    v___x_3206_,
                                                    v___x_3171_,
                                                );
                                                v___x_3208_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13;
                                                v___x_3209_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
                                                leanh::lean_inc_n(v___x_3207_, 4);
                                                v___x_3210_ =
                                                    leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                                leanh::lean_ctor_set(
                                                    v___x_3210_,
                                                    0,
                                                    v___x_3207_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3210_,
                                                    1,
                                                    v___x_3208_,
                                                );
                                                leanh::lean_ctor_set(
                                                    v___x_3210_,
                                                    2,
                                                    v___x_3209_,
                                                );
                                                v___x_3211_ = l_Lean_Syntax_node1(
                                                    v___x_3207_,
                                                    v___x_3189_,
                                                    v___x_3210_,
                                                );
                                                leanh::lean_inc(v___x_3172_);
                                                v___x_3212_ = l_Lean_Syntax_node1(
                                                    v___x_3207_,
                                                    v___x_3208_,
                                                    v___x_3172_,
                                                );
                                                v___x_3213_ = l_Lean_Syntax_node2(
                                                    v___x_3207_,
                                                    v___x_3195_,
                                                    v_attr_3198_,
                                                    v___x_3212_,
                                                );
                                                v___x_3214_ = l_Lean_Syntax_node2(
                                                    v___x_3207_,
                                                    v___x_3177_,
                                                    v___x_3211_,
                                                    v___x_3213_,
                                                );
                                                v___y_3182_ = v___x_3214_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3183_ = 1usize;
                v___x_3184_ = lean_usize_add(v_i_3174_, v___x_3183_);
                v___x_3185_ = lean_array_uset(v_bs_x27_3180_, v_i_3174_, v___y_3182_);
                v_i_3174_ = v___x_3184_;
                v_bs_3175_ = v___x_3185_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___boxed(
    mut v___x_3215_: *mut leanh::LeanObject,
    mut v___x_3216_: *mut leanh::LeanObject,
    mut v_sz_3217_: *mut leanh::LeanObject,
    mut v_i_3218_: *mut leanh::LeanObject,
    mut v_bs_3219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_10694__boxed_3220_: u8 = 0;
    let mut v_sz_boxed_3221_: usize = 0;
    let mut v_i_boxed_3222_: usize = 0;
    let mut v_res_3223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_10694__boxed_3220_ = (leanh::lean_unbox(v___x_3215_) as u8);
    v_sz_boxed_3221_ = leanh::lean_unbox_usize(v_sz_3217_);
    leanh::lean_dec(v_sz_3217_);
    v_i_boxed_3222_ = leanh::lean_unbox_usize(v_i_3218_);
    leanh::lean_dec(v_i_3218_);
    v_res_3223_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_10694__boxed_3220_, v___x_3216_, v_sz_boxed_3221_, v_i_boxed_3222_, v_bs_3219_);
    return v_res_3223_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3224_: u8 = 0;
    let mut v___x_3225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3224_ = 0;
    v___x_3225_ = leanh::lean_box(0);
    v___x_3226_ = l_Lean_SourceInfo_fromRef(v___x_3225_, v___x_3224_);
    return v___x_3226_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_3227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3227_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
    v___x_3228_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13;
    v___x_3229_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
    v___x_3230_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3230_, 0, v___x_3229_);
    leanh::lean_ctor_set(v___x_3230_, 1, v___x_3228_);
    leanh::lean_ctor_set(v___x_3230_, 2, v___x_3227_);
    return v___x_3230_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3231_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__1);
    v___x_3232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6;
    v___x_3233_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
    v___x_3234_ = l_Lean_Syntax_node1(v___x_3233_, v___x_3232_, v___x_3231_);
    return v___x_3234_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(
    mut v___x_3235_: *mut leanh::LeanObject,
    mut v_sz_3236_: usize,
    mut v_i_3237_: usize,
    mut v_bs_3238_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3239_: u8 = 0;
    let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: usize = 0;
    let mut v___x_3247_: usize = 0;
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: u8 = 0;
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: u8 = 0;
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: u8 = 0;
    let mut v___x_3256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: u8 = 0;
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: u8 = 0;
    let mut v___x_3265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3239_ = lean_usize_dec_lt(v_i_3237_, v_sz_3236_);
                if v___x_3239_ == 0 {
                    leanh::lean_dec(v___x_3235_);
                    return v_bs_3238_;
                } else {
                    v___x_3240_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4;
                    v_v_3241_ = lean_array_uget(v_bs_3238_, v_i_3237_);
                    v___x_3242_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3243_ = lean_array_uset(v_bs_3238_, v_i_3237_, v___x_3242_);
                    leanh::lean_inc(v_v_3241_);
                    v___x_3250_ = l_Lean_Syntax_isOfKind(v_v_3241_, v___x_3240_);
                    if v___x_3250_ == 0 {
                        v___y_3245_ = v_v_3241_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3251_ = l_Lean_Syntax_getArg(v_v_3241_, v___x_3242_);
                        v___x_3252_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6;
                        leanh::lean_inc(v___x_3251_);
                        v___x_3253_ = l_Lean_Syntax_isOfKind(v___x_3251_, v___x_3252_);
                        if v___x_3253_ == 0 {
                            leanh::lean_dec(v___x_3251_);
                            v___y_3245_ = v_v_3241_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3254_ = l_Lean_Syntax_getArg(v___x_3251_, v___x_3242_);
                            leanh::lean_dec(v___x_3251_);
                            v___x_3255_ = l_Lean_Syntax_matchesNull(v___x_3254_, v___x_3242_);
                            if v___x_3255_ == 0 {
                                v___y_3245_ = v_v_3241_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3256_ = leanh::lean_unsigned_to_nat(1);
                                v___x_3257_ = l_Lean_Syntax_getArg(v_v_3241_, v___x_3256_);
                                v___x_3258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9;
                                leanh::lean_inc(v___x_3257_);
                                v___x_3259_ = l_Lean_Syntax_isOfKind(v___x_3257_, v___x_3258_);
                                if v___x_3259_ == 0 {
                                    leanh::lean_dec(v___x_3257_);
                                    v___y_3245_ = v_v_3241_;
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3260_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                                    v_attr_3261_ = l_Lean_Syntax_getArg(v___x_3257_, v___x_3242_);
                                    leanh::lean_inc(v_attr_3261_);
                                    v___x_3262_ = l_Lean_Syntax_isOfKind(v_attr_3261_, v___x_3260_);
                                    if v___x_3262_ == 0 {
                                        leanh::lean_dec(v_attr_3261_);
                                        leanh::lean_dec(v___x_3257_);
                                        v___y_3245_ = v_v_3241_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3263_ =
                                            l_Lean_Syntax_getArg(v___x_3257_, v___x_3256_);
                                        leanh::lean_dec(v___x_3257_);
                                        v___x_3264_ =
                                            l_Lean_Syntax_matchesNull(v___x_3263_, v___x_3242_);
                                        if v___x_3264_ == 0 {
                                            leanh::lean_dec(v_attr_3261_);
                                            v___y_3245_ = v_v_3241_;
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3265_ = l_Lean_TSyntax_getId(v_attr_3261_);
                                            v___x_3266_ = lean_erase_macro_scopes(v___x_3265_);
                                            v___x_3267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__11;
                                            v___x_3268_ = lean_name_eq(v___x_3266_, v___x_3267_);
                                            leanh::lean_dec(v___x_3266_);
                                            if v___x_3268_ == 0 {
                                                leanh::lean_dec(v_attr_3261_);
                                                v___y_3245_ = v_v_3241_;
                                                state = 1;
                                                continue;
                                            } else {
                                                leanh::lean_dec(v_v_3241_);
                                                v___x_3269_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__0);
                                                v___x_3270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13;
                                                v___x_3271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___closed__2);
                                                leanh::lean_inc(v___x_3235_);
                                                v___x_3272_ = l_Lean_Syntax_node1(
                                                    v___x_3269_,
                                                    v___x_3270_,
                                                    v___x_3235_,
                                                );
                                                v___x_3273_ = l_Lean_Syntax_node2(
                                                    v___x_3269_,
                                                    v___x_3258_,
                                                    v_attr_3261_,
                                                    v___x_3272_,
                                                );
                                                v___x_3274_ = l_Lean_Syntax_node2(
                                                    v___x_3269_,
                                                    v___x_3240_,
                                                    v___x_3271_,
                                                    v___x_3273_,
                                                );
                                                v___y_3245_ = v___x_3274_;
                                                state = 1;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3246_ = 1usize;
                v___x_3247_ = lean_usize_add(v_i_3237_, v___x_3246_);
                v___x_3248_ = lean_array_uset(v_bs_x27_3243_, v_i_3237_, v___y_3245_);
                v_i_3237_ = v___x_3247_;
                v_bs_3238_ = v___x_3248_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1___boxed(
    mut v___x_3275_: *mut leanh::LeanObject,
    mut v_sz_3276_: *mut leanh::LeanObject,
    mut v_i_3277_: *mut leanh::LeanObject,
    mut v_bs_3278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3279_: usize = 0;
    let mut v_i_boxed_3280_: usize = 0;
    let mut v_res_3281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3279_ = leanh::lean_unbox_usize(v_sz_3276_);
    leanh::lean_dec(v_sz_3276_);
    v_i_boxed_3280_ = leanh::lean_unbox_usize(v_i_3277_);
    leanh::lean_dec(v_i_3277_);
    v_res_3281_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_3275_, v_sz_boxed_3279_, v_i_boxed_3280_, v_bs_3278_);
    return v_res_3281_;
}
pub unsafe fn l_Lean_Elab_Command_addInheritDocDefault(
    mut v_rhs_3289_: *mut leanh::LeanObject,
    mut v_attrs_x3f_3290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    let mut v___x_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3298_: u8 = 0;
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3301_: usize = 0;
    let mut v___x_3302_: usize = 0;
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v_unused_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: u8 = 0;
    let mut v___x_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3316_: u8 = 0;
    let mut v___x_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3319_: usize = 0;
    let mut v___x_3320_: usize = 0;
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3326_: u8 = 0;
    let mut v_unused_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_attrs_x3f_3290_) == 0 {
                    leanh::lean_dec(v_rhs_3289_);
                    return v_attrs_x3f_3290_;
                } else {
                    v_val_3291_ = leanh::lean_ctor_get(v_attrs_x3f_3290_, 0);
                    v___x_3292_ = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
                    leanh::lean_inc(v_rhs_3289_);
                    v___x_3293_ = l_Lean_Syntax_isOfKind(v_rhs_3289_, v___x_3292_);
                    if v___x_3293_ == 0 {
                        v___x_3294_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                        leanh::lean_inc(v_rhs_3289_);
                        v___x_3295_ = l_Lean_Syntax_isOfKind(v_rhs_3289_, v___x_3294_);
                        if v___x_3295_ == 0 {
                            leanh::lean_dec(v_rhs_3289_);
                            return v_attrs_x3f_3290_;
                        } else {
                            leanh::lean_inc(v_val_3291_);
                            v_isSharedCheck_3308_ =
                                (!leanh::lean_is_exclusive(v_attrs_x3f_3290_)) as u8;
                            if v_isSharedCheck_3308_ == 0 {
                                v_unused_3309_ = leanh::lean_ctor_get(v_attrs_x3f_3290_, 0);
                                leanh::lean_dec(v_unused_3309_);
                                v___x_3297_ = v_attrs_x3f_3290_;
                                v_isShared_3298_ = v_isSharedCheck_3308_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v_attrs_x3f_3290_);
                                v___x_3297_ = leanh::lean_box(0);
                                v_isShared_3298_ = v_isSharedCheck_3308_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_3310_ = leanh::lean_unsigned_to_nat(0);
                        v___x_3311_ = l_Lean_Syntax_getArg(v_rhs_3289_, v___x_3310_);
                        leanh::lean_dec(v_rhs_3289_);
                        v___x_3312_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                        leanh::lean_inc(v___x_3311_);
                        v___x_3313_ = l_Lean_Syntax_isOfKind(v___x_3311_, v___x_3312_);
                        if v___x_3313_ == 0 {
                            leanh::lean_dec(v___x_3311_);
                            return v_attrs_x3f_3290_;
                        } else {
                            leanh::lean_inc(v_val_3291_);
                            v_isSharedCheck_3326_ =
                                (!leanh::lean_is_exclusive(v_attrs_x3f_3290_)) as u8;
                            if v_isSharedCheck_3326_ == 0 {
                                v_unused_3327_ = leanh::lean_ctor_get(v_attrs_x3f_3290_, 0);
                                leanh::lean_dec(v_unused_3327_);
                                v___x_3315_ = v_attrs_x3f_3290_;
                                v_isShared_3316_ = v_isSharedCheck_3326_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_attrs_x3f_3290_);
                                v___x_3315_ = leanh::lean_box(0);
                                v_isShared_3316_ = v_isSharedCheck_3326_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3299_ = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
                v___x_3300_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3291_);
                leanh::lean_dec(v_val_3291_);
                v_sz_3301_ = lean_array_size(v___x_3300_);
                v___x_3302_ = 0usize;
                v___x_3303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0(v___x_3293_, v_rhs_3289_, v_sz_3301_, v___x_3302_, v___x_3300_);
                v___x_3304_ = l_Lean_Syntax_SepArray_ofElems(v___x_3299_, v___x_3303_);
                leanh::lean_dec_ref(v___x_3303_);
                if v_isShared_3298_ == 0 {
                    leanh::lean_ctor_set(v___x_3297_, 0, v___x_3304_);
                    v___x_3306_ = v___x_3297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3306_;
            }
            3 => {
                v___x_3317_ = l_Lean_Elab_Command_addInheritDocDefault___closed__2;
                v___x_3318_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3291_);
                leanh::lean_dec(v_val_3291_);
                v_sz_3319_ = lean_array_size(v___x_3318_);
                v___x_3320_ = 0usize;
                v___x_3321_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__1(v___x_3311_, v_sz_3319_, v___x_3320_, v___x_3318_);
                v___x_3322_ = l_Lean_Syntax_SepArray_ofElems(v___x_3317_, v___x_3321_);
                leanh::lean_dec_ref(v___x_3321_);
                if v_isShared_3316_ == 0 {
                    leanh::lean_ctor_set(v___x_3315_, 0, v___x_3322_);
                    v___x_3324_ = v___x_3315_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3325_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3322_);
                    v___x_3324_ = v_reuseFailAlloc_3325_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3335_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__2;
    v___x_3336_ = l_String_toRawSubstring_x27(v___x_3335_);
    return v___x_3336_;
}
pub unsafe fn l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(
    mut v_x_3367_: *mut leanh::LeanObject,
    mut v_a_3368_: *mut leanh::LeanObject,
    mut v_a_3369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_3383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: u8 = 0;
    let mut v___x_3390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: u8 = 0;
    let mut v___x_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: u8 = 0;
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: u8 = 0;
    let mut v___x_3423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: u8 = 0;
    let mut v___x_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3429_: u8 = 0;
    let mut v___x_3430_: u8 = 0;
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: u8 = 0;
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: u8 = 0;
    let mut v___x_3438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: u8 = 0;
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3406_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
                leanh::lean_inc(v_x_3367_);
                v___x_3407_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3406_);
                if v___x_3407_ == 0 {
                    v___x_3408_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12;
                    leanh::lean_inc(v_x_3367_);
                    v___x_3409_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3408_);
                    if v___x_3409_ == 0 {
                        v___x_3410_ =
                            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
                        leanh::lean_inc(v_x_3367_);
                        v___x_3411_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3410_);
                        if v___x_3411_ == 0 {
                            leanh::lean_dec(v_x_3367_);
                            v___x_3412_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3369_);
                            return v___x_3412_;
                        } else {
                            v___x_3413_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3413_, 0, v_x_3367_);
                            leanh::lean_ctor_set(v___x_3413_, 1, v_a_3369_);
                            return v___x_3413_;
                        }
                    } else {
                        v_ref_3414_ = leanh::lean_ctor_get(v_a_3368_, 5);
                        v___x_3415_ = l_Lean_SourceInfo_fromRef(v_ref_3414_, v___x_3407_);
                        v___x_3416_ =
                            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__16;
                        v___x_3417_ = l_Lean_Syntax_node1(v___x_3415_, v___x_3416_, v_x_3367_);
                        v___x_3418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3418_, 0, v___x_3417_);
                        leanh::lean_ctor_set(v___x_3418_, 1, v_a_3369_);
                        return v___x_3418_;
                    }
                } else {
                    v___x_3419_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3420_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_3419_);
                    v___x_3421_ =
                        l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                    v___x_3422_ = l_Lean_Syntax_isOfKind(v___x_3420_, v___x_3421_);
                    if v___x_3422_ == 0 {
                        v___x_3423_ =
                            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
                        leanh::lean_inc(v_x_3367_);
                        v___x_3424_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3423_);
                        if v___x_3424_ == 0 {
                            leanh::lean_dec(v_x_3367_);
                            v___x_3425_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3369_);
                            return v___x_3425_;
                        } else {
                            v___x_3426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3426_, 0, v_x_3367_);
                            leanh::lean_ctor_set(v___x_3426_, 1, v_a_3369_);
                            return v___x_3426_;
                        }
                    } else {
                        v___x_3427_ = leanh::lean_unsigned_to_nat(1);
                        v___x_3428_ = l_Lean_Syntax_getArg(v_x_3367_, v___x_3427_);
                        v___x_3429_ = l_Lean_Syntax_isNone(v___x_3428_);
                        if v___x_3429_ == 0 {
                            leanh::lean_inc(v___x_3428_);
                            v___x_3430_ = l_Lean_Syntax_matchesNull(v___x_3428_, v___x_3427_);
                            if v___x_3430_ == 0 {
                                leanh::lean_dec(v___x_3428_);
                                v___x_3431_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
                                leanh::lean_inc(v_x_3367_);
                                v___x_3432_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3431_);
                                if v___x_3432_ == 0 {
                                    leanh::lean_dec(v_x_3367_);
                                    v___x_3433_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3369_);
                                    return v___x_3433_;
                                } else {
                                    v___x_3434_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3434_, 0, v_x_3367_);
                                    leanh::lean_ctor_set(v___x_3434_, 1, v_a_3369_);
                                    return v___x_3434_;
                                }
                            } else {
                                v___x_3435_ = l_Lean_Syntax_getArg(v___x_3428_, v___x_3419_);
                                leanh::lean_dec(v___x_3428_);
                                v___x_3436_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
                                leanh::lean_inc(v___x_3435_);
                                v___x_3437_ = l_Lean_Syntax_isOfKind(v___x_3435_, v___x_3436_);
                                if v___x_3437_ == 0 {
                                    leanh::lean_dec(v___x_3435_);
                                    v___x_3438_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
                                    leanh::lean_inc(v_x_3367_);
                                    v___x_3439_ = l_Lean_Syntax_isOfKind(v_x_3367_, v___x_3438_);
                                    if v___x_3439_ == 0 {
                                        leanh::lean_dec(v_x_3367_);
                                        v___x_3440_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3369_);
                                        return v___x_3440_;
                                    } else {
                                        v___x_3441_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(v___x_3441_, 0, v_x_3367_);
                                        leanh::lean_ctor_set(v___x_3441_, 1, v_a_3369_);
                                        return v___x_3441_;
                                    }
                                } else {
                                    leanh::lean_dec(v_x_3367_);
                                    v_prec_x3f_3442_ =
                                        l_Lean_Syntax_getArg(v___x_3435_, v___x_3427_);
                                    leanh::lean_dec(v___x_3435_);
                                    v___x_3443_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_3443_, 0, v_prec_x3f_3442_);
                                    v_prec_x3f_3383_ = v___x_3443_;
                                    v___y_3384_ = v_a_3368_;
                                    v___y_3385_ = v_a_3369_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v___x_3428_);
                            leanh::lean_dec(v_x_3367_);
                            v___x_3444_ = leanh::lean_box(0);
                            v_prec_x3f_3383_ = v___x_3444_;
                            v___y_3384_ = v_a_3368_;
                            v___y_3385_ = v_a_3369_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_3376_);
                v___x_3378_ = l_Array_append___redArg(v___y_3376_, v___y_3377_);
                leanh::lean_dec_ref(v___y_3377_);
                leanh::lean_inc(v___y_3371_);
                leanh::lean_inc(v___y_3374_);
                v___x_3379_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_3379_, 0, v___y_3374_);
                leanh::lean_ctor_set(v___x_3379_, 1, v___y_3371_);
                leanh::lean_ctor_set(v___x_3379_, 2, v___x_3378_);
                leanh::lean_inc(v___y_3372_);
                v___x_3380_ =
                    l_Lean_Syntax_node2(v___y_3374_, v___y_3372_, v___y_3375_, v___x_3379_);
                v___x_3381_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3381_, 0, v___x_3380_);
                leanh::lean_ctor_set(v___x_3381_, 1, v___y_3373_);
                return v___x_3381_;
            }
            2 => {
                v_quotContext_3386_ = leanh::lean_ctor_get(v___y_3384_, 1);
                v_currMacroScope_3387_ = leanh::lean_ctor_get(v___y_3384_, 2);
                v_ref_3388_ = leanh::lean_ctor_get(v___y_3384_, 5);
                v___x_3389_ = 0;
                v___x_3390_ = l_Lean_SourceInfo_fromRef(v_ref_3388_, v___x_3389_);
                v___x_3391_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__2;
                v___x_3392_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3_once
                    ),
                    _init_l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__3,
                );
                v___x_3393_ =
                    l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
                leanh::lean_inc(v_currMacroScope_3387_);
                leanh::lean_inc(v_quotContext_3386_);
                v___x_3394_ =
                    l_Lean_addMacroScope(v_quotContext_3386_, v___x_3393_, v_currMacroScope_3387_);
                v___x_3395_ = leanh::lean_box(0);
                leanh::lean_inc(v___x_3390_);
                v___x_3396_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_3396_, 0, v___x_3390_);
                leanh::lean_ctor_set(v___x_3396_, 1, v___x_3392_);
                leanh::lean_ctor_set(v___x_3396_, 2, v___x_3394_);
                leanh::lean_ctor_set(v___x_3396_, 3, v___x_3395_);
                v___x_3397_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13;
                v___x_3398_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
                if leanh::lean_obj_tag(v_prec_x3f_3383_) == 1 {
                    v_val_3399_ = leanh::lean_ctor_get(v_prec_x3f_3383_, 0);
                    leanh::lean_inc(v_val_3399_);
                    leanh::lean_dec_ref_known(v_prec_x3f_3383_, 1);
                    v___x_3400_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
                    v___x_3401_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
                    leanh::lean_inc_n(v___x_3390_, 2);
                    v___x_3402_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3402_, 0, v___x_3390_);
                    leanh::lean_ctor_set(v___x_3402_, 1, v___x_3401_);
                    v___x_3403_ =
                        l_Lean_Syntax_node2(v___x_3390_, v___x_3400_, v___x_3402_, v_val_3399_);
                    v___x_3404_ = l_Array_mkArray1___redArg(v___x_3403_);
                    v___y_3371_ = v___x_3397_;
                    v___y_3372_ = v___x_3391_;
                    v___y_3373_ = v___y_3385_;
                    v___y_3374_ = v___x_3390_;
                    v___y_3375_ = v___x_3396_;
                    v___y_3376_ = v___x_3398_;
                    v___y_3377_ = v___x_3404_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_prec_x3f_3383_);
                    v___x_3405_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
                    v___y_3371_ = v___x_3397_;
                    v___y_3372_ = v___x_3391_;
                    v___y_3373_ = v___y_3385_;
                    v___y_3374_ = v___x_3390_;
                    v___y_3375_ = v___x_3396_;
                    v___y_3376_ = v___x_3398_;
                    v___y_3377_ = v___x_3405_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___boxed(
    mut v_x_3445_: *mut leanh::LeanObject,
    mut v_a_3446_: *mut leanh::LeanObject,
    mut v_a_3447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3448_ =
        l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(v_x_3445_, v_a_3446_, v_a_3447_);
    leanh::lean_dec_ref(v_a_3446_);
    return v_res_3448_;
}
pub unsafe fn l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(
    mut v_stx_3449_: *mut leanh::LeanObject,
    mut v_a_3450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3452_: u8 = 0;
    let mut v___x_3453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: u8 = 0;
    let mut v___x_3464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v___x_3466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_stx_3449_);
                v_k_3459_ = l_Lean_Syntax_getKind(v_stx_3449_);
                v___x_3460_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
                v___x_3461_ = lean_name_eq(v_k_3459_, v___x_3460_);
                if v___x_3461_ == 0 {
                    v___x_3462_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__12;
                    v___x_3463_ = lean_name_eq(v_k_3459_, v___x_3462_);
                    if v___x_3463_ == 0 {
                        v___x_3464_ =
                            l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__14;
                        v___x_3465_ = lean_name_eq(v_k_3459_, v___x_3464_);
                        leanh::lean_dec(v_k_3459_);
                        if v___x_3465_ == 0 {
                            leanh::lean_dec(v_stx_3449_);
                            v___x_3466_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3450_);
                            return v___x_3466_;
                        } else {
                            v___x_3467_ = leanh::lean_unsigned_to_nat(4);
                            v___x_3468_ = l_Lean_Syntax_getArg(v_stx_3449_, v___x_3467_);
                            v___x_3469_ = l_Lean_Syntax_isNone(v___x_3468_);
                            leanh::lean_dec(v___x_3468_);
                            if v___x_3469_ == 0 {
                                v___y_3452_ = v___x_3465_;
                                state = 1;
                                continue;
                            } else {
                                v___y_3452_ = v___x_3463_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_k_3459_);
                        v___x_3470_ =
                            l_Lean_Elab_Command_strLitToPattern___redArg(v_stx_3449_, v_a_3450_);
                        leanh::lean_dec(v_stx_3449_);
                        return v___x_3470_;
                    }
                } else {
                    leanh::lean_dec(v_k_3459_);
                    v___x_3471_ =
                        l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
                    v___x_3472_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3473_ = l_Lean_Syntax_getArg(v_stx_3449_, v___x_3472_);
                    leanh::lean_dec(v_stx_3449_);
                    v___x_3474_ = leanh::lean_box(0);
                    v___x_3475_ = l_Lean_Syntax_mkAntiquotNode(
                        v___x_3471_,
                        v___x_3473_,
                        v___x_3472_,
                        v___x_3474_,
                        v___x_3461_,
                    );
                    v___x_3476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3476_, 0, v___x_3475_);
                    leanh::lean_ctor_set(v___x_3476_, 1, v_a_3450_);
                    return v___x_3476_;
                }
            }
            1 => {
                if v___y_3452_ == 0 {
                    v___x_3453_ = leanh::lean_unsigned_to_nat(1);
                    v___x_3454_ = l_Lean_Syntax_getArg(v_stx_3449_, v___x_3453_);
                    leanh::lean_dec(v_stx_3449_);
                    v___x_3455_ =
                        l_Lean_Elab_Command_strLitToPattern___redArg(v___x_3454_, v_a_3450_);
                    leanh::lean_dec(v___x_3454_);
                    return v___x_3455_;
                } else {
                    v___x_3456_ = leanh::lean_unsigned_to_nat(3);
                    v___x_3457_ = l_Lean_Syntax_getArg(v_stx_3449_, v___x_3456_);
                    leanh::lean_dec(v_stx_3449_);
                    v___x_3458_ =
                        l_Lean_Elab_Command_strLitToPattern___redArg(v___x_3457_, v_a_3450_);
                    leanh::lean_dec(v___x_3457_);
                    return v___x_3458_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_expandNotationItemIntoPattern(
    mut v_stx_3477_: *mut leanh::LeanObject,
    mut v_a_3478_: *mut leanh::LeanObject,
    mut v_a_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ =
        l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(v_stx_3477_, v_a_3479_);
    return v___x_3480_;
}
pub unsafe fn l_Lean_Elab_Command_expandNotationItemIntoPattern___boxed(
    mut v_stx_3481_: *mut leanh::LeanObject,
    mut v_a_3482_: *mut leanh::LeanObject,
    mut v_a_3483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3484_ =
        l_Lean_Elab_Command_expandNotationItemIntoPattern(v_stx_3481_, v_a_3482_, v_a_3483_);
    leanh::lean_dec_ref(v_a_3482_);
    return v_res_3484_;
}
pub unsafe fn l_Lean_Elab_Command_removeParenthesesAux(
    mut v_parens_3485_: *mut leanh::LeanObject,
    mut v_body_3486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leading_3488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_3491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_leading_3494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_3495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_3496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3499_: u8 = 0;
    let mut v___x_3500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_trailing_3501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3504_: u8 = 0;
    let mut v___x_3506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3513_: u8 = 0;
    let mut v_unused_3514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_unused_3518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3487_ = l_Lean_Syntax_getHeadInfo(v_parens_3485_);
                if leanh::lean_obj_tag(v___x_3487_) == 0 {
                    v_leading_3488_ = leanh::lean_ctor_get(v___x_3487_, 0);
                    leanh::lean_inc_ref(v_leading_3488_);
                    leanh::lean_dec_ref_known(v___x_3487_, 4);
                    v___x_3489_ = l_Lean_Syntax_getHeadInfo(v_body_3486_);
                    if leanh::lean_obj_tag(v___x_3489_) == 0 {
                        v_pos_3490_ = leanh::lean_ctor_get(v___x_3489_, 1);
                        leanh::lean_inc(v_pos_3490_);
                        v_trailing_3491_ = leanh::lean_ctor_get(v___x_3489_, 2);
                        leanh::lean_inc_ref(v_trailing_3491_);
                        v_endPos_3492_ = leanh::lean_ctor_get(v___x_3489_, 3);
                        leanh::lean_inc(v_endPos_3492_);
                        leanh::lean_dec_ref_known(v___x_3489_, 4);
                        v___x_3493_ = l_Lean_Syntax_getTailInfo(v_body_3486_);
                        if leanh::lean_obj_tag(v___x_3493_) == 0 {
                            v_leading_3494_ = leanh::lean_ctor_get(v___x_3493_, 0);
                            v_pos_3495_ = leanh::lean_ctor_get(v___x_3493_, 1);
                            v_endPos_3496_ = leanh::lean_ctor_get(v___x_3493_, 3);
                            v_isSharedCheck_3517_ =
                                (!leanh::lean_is_exclusive(v___x_3493_)) as u8;
                            if v_isSharedCheck_3517_ == 0 {
                                v_unused_3518_ = leanh::lean_ctor_get(v___x_3493_, 2);
                                leanh::lean_dec(v_unused_3518_);
                                v___x_3498_ = v___x_3493_;
                                v_isShared_3499_ = v_isSharedCheck_3517_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_endPos_3496_);
                                leanh::lean_inc(v_pos_3495_);
                                leanh::lean_inc(v_leading_3494_);
                                leanh::lean_dec(v___x_3493_);
                                v___x_3498_ = leanh::lean_box(0);
                                v_isShared_3499_ = v_isSharedCheck_3517_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_3493_);
                            leanh::lean_dec(v_endPos_3492_);
                            leanh::lean_dec_ref(v_trailing_3491_);
                            leanh::lean_dec(v_pos_3490_);
                            leanh::lean_dec_ref(v_leading_3488_);
                            return v_body_3486_;
                        }
                    } else {
                        leanh::lean_dec(v___x_3489_);
                        leanh::lean_dec_ref(v_leading_3488_);
                        return v_body_3486_;
                    }
                } else {
                    leanh::lean_dec(v___x_3487_);
                    return v_body_3486_;
                }
            }
            1 => {
                v___x_3500_ = l_Lean_Syntax_getTailInfo(v_parens_3485_);
                if leanh::lean_obj_tag(v___x_3500_) == 0 {
                    v_trailing_3501_ = leanh::lean_ctor_get(v___x_3500_, 2);
                    v_isSharedCheck_3513_ = (!leanh::lean_is_exclusive(v___x_3500_)) as u8;
                    if v_isSharedCheck_3513_ == 0 {
                        v_unused_3514_ = leanh::lean_ctor_get(v___x_3500_, 3);
                        leanh::lean_dec(v_unused_3514_);
                        v_unused_3515_ = leanh::lean_ctor_get(v___x_3500_, 1);
                        leanh::lean_dec(v_unused_3515_);
                        v_unused_3516_ = leanh::lean_ctor_get(v___x_3500_, 0);
                        leanh::lean_dec(v_unused_3516_);
                        v___x_3503_ = v___x_3500_;
                        v_isShared_3504_ = v_isSharedCheck_3513_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_trailing_3501_);
                        leanh::lean_dec(v___x_3500_);
                        v___x_3503_ = leanh::lean_box(0);
                        v_isShared_3504_ = v_isSharedCheck_3513_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_3500_);
                    leanh::lean_del_object(v___x_3498_);
                    leanh::lean_dec(v_endPos_3496_);
                    leanh::lean_dec(v_pos_3495_);
                    leanh::lean_dec_ref(v_leading_3494_);
                    leanh::lean_dec(v_endPos_3492_);
                    leanh::lean_dec_ref(v_trailing_3491_);
                    leanh::lean_dec(v_pos_3490_);
                    leanh::lean_dec_ref(v_leading_3488_);
                    return v_body_3486_;
                }
            }
            2 => {
                if v_isShared_3504_ == 0 {
                    leanh::lean_ctor_set(v___x_3503_, 3, v_endPos_3492_);
                    leanh::lean_ctor_set(v___x_3503_, 2, v_trailing_3491_);
                    leanh::lean_ctor_set(v___x_3503_, 1, v_pos_3490_);
                    leanh::lean_ctor_set(v___x_3503_, 0, v_leading_3488_);
                    v___x_3506_ = v___x_3503_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3512_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_leading_3488_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3512_, 1, v_pos_3490_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3512_, 2, v_trailing_3491_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3512_, 3, v_endPos_3492_);
                    v___x_3506_ = v_reuseFailAlloc_3512_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3507_ = l_Lean_Syntax_setHeadInfo(v_body_3486_, v___x_3506_);
                if v_isShared_3499_ == 0 {
                    leanh::lean_ctor_set(v___x_3498_, 2, v_trailing_3501_);
                    v___x_3509_ = v___x_3498_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3511_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_leading_3494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_pos_3495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 2, v_trailing_3501_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3511_, 3, v_endPos_3496_);
                    v___x_3509_ = v_reuseFailAlloc_3511_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3510_ = l_Lean_Syntax_setTailInfo(v___x_3507_, v___x_3509_);
                return v___x_3510_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_removeParenthesesAux___boxed(
    mut v_parens_3519_: *mut leanh::LeanObject,
    mut v_body_3520_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Lean_Elab_Command_removeParenthesesAux(v_parens_3519_, v_body_3520_);
    leanh::lean_dec(v_parens_3519_);
    return v_res_3521_;
}
pub unsafe fn l_Lean_Elab_Command_removeParentheses(
    mut v_stx_3537_: *mut leanh::LeanObject,
    mut v_a_3538_: *mut leanh::LeanObject,
    mut v_a_3539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: u8 = 0;
    let mut v_info_3542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3547_: u8 = 0;
    let mut v_sz_3548_: usize = 0;
    let mut v___x_3549_: usize = 0;
    let mut v___x_3550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3555_: u8 = 0;
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3567_: u8 = 0;
    let mut v___x_3569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3571_: u8 = 0;
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3577_: u8 = 0;
    let mut v_info_3578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3583_: u8 = 0;
    let mut v_sz_3584_: usize = 0;
    let mut v___x_3585_: usize = 0;
    let mut v___x_3586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3591_: u8 = 0;
    let mut v___x_3593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3598_: u8 = 0;
    let mut v_a_3599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3603_: u8 = 0;
    let mut v___x_3605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3607_: u8 = 0;
    let mut v_isSharedCheck_3608_: u8 = 0;
    let mut v___x_3609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_h_3611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v_info_3614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3619_: u8 = 0;
    let mut v_sz_3620_: usize = 0;
    let mut v___x_3621_: usize = 0;
    let mut v___x_3622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3634_: u8 = 0;
    let mut v_a_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3639_: u8 = 0;
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3643_: u8 = 0;
    let mut v_isSharedCheck_3644_: u8 = 0;
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_3646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3664_: u8 = 0;
    let mut v_val_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3670_: u8 = 0;
    let mut v___x_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3540_ = l_Lean_Elab_Command_removeParentheses___closed__1;
                leanh::lean_inc(v_stx_3537_);
                v___x_3541_ = l_Lean_Syntax_isOfKind(v_stx_3537_, v___x_3540_);
                if v___x_3541_ == 0 {
                    if leanh::lean_obj_tag(v_stx_3537_) == 1 {
                        v_info_3542_ = leanh::lean_ctor_get(v_stx_3537_, 0);
                        v_kind_3543_ = leanh::lean_ctor_get(v_stx_3537_, 1);
                        v_args_3544_ = leanh::lean_ctor_get(v_stx_3537_, 2);
                        v_isSharedCheck_3572_ =
                            (!leanh::lean_is_exclusive(v_stx_3537_)) as u8;
                        if v_isSharedCheck_3572_ == 0 {
                            v___x_3546_ = v_stx_3537_;
                            v_isShared_3547_ = v_isSharedCheck_3572_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_args_3544_);
                            leanh::lean_inc(v_kind_3543_);
                            leanh::lean_inc(v_info_3542_);
                            leanh::lean_dec(v_stx_3537_);
                            v___x_3546_ = leanh::lean_box(0);
                            v_isShared_3547_ = v_isSharedCheck_3572_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_3573_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_3573_, 0, v_stx_3537_);
                        leanh::lean_ctor_set(v___x_3573_, 1, v_a_3539_);
                        return v___x_3573_;
                    }
                } else {
                    v___x_3574_ = leanh::lean_unsigned_to_nat(0);
                    v___x_3575_ = l_Lean_Syntax_getArg(v_stx_3537_, v___x_3574_);
                    v___x_3576_ = l_Lean_Elab_Command_removeParentheses___closed__3;
                    leanh::lean_inc(v___x_3575_);
                    v___x_3577_ = l_Lean_Syntax_isOfKind(v___x_3575_, v___x_3576_);
                    if v___x_3577_ == 0 {
                        leanh::lean_dec(v___x_3575_);
                        if leanh::lean_obj_tag(v_stx_3537_) == 1 {
                            v_info_3578_ = leanh::lean_ctor_get(v_stx_3537_, 0);
                            v_kind_3579_ = leanh::lean_ctor_get(v_stx_3537_, 1);
                            v_args_3580_ = leanh::lean_ctor_get(v_stx_3537_, 2);
                            v_isSharedCheck_3608_ =
                                (!leanh::lean_is_exclusive(v_stx_3537_)) as u8;
                            if v_isSharedCheck_3608_ == 0 {
                                v___x_3582_ = v_stx_3537_;
                                v_isShared_3583_ = v_isSharedCheck_3608_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_args_3580_);
                                leanh::lean_inc(v_kind_3579_);
                                leanh::lean_inc(v_info_3578_);
                                leanh::lean_dec(v_stx_3537_);
                                v___x_3582_ = leanh::lean_box(0);
                                v_isShared_3583_ = v_isSharedCheck_3608_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_3609_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_3609_, 0, v_stx_3537_);
                            leanh::lean_ctor_set(v___x_3609_, 1, v_a_3539_);
                            return v___x_3609_;
                        }
                    } else {
                        v___x_3610_ = leanh::lean_unsigned_to_nat(1);
                        v_h_3611_ = l_Lean_Syntax_getArg(v___x_3575_, v___x_3610_);
                        leanh::lean_dec(v___x_3575_);
                        v___x_3612_ = l_Lean_Elab_Command_removeParentheses___closed__5;
                        leanh::lean_inc(v_h_3611_);
                        v___x_3613_ = l_Lean_Syntax_isOfKind(v_h_3611_, v___x_3612_);
                        if v___x_3613_ == 0 {
                            leanh::lean_dec(v_h_3611_);
                            if leanh::lean_obj_tag(v_stx_3537_) == 1 {
                                v_info_3614_ = leanh::lean_ctor_get(v_stx_3537_, 0);
                                v_kind_3615_ = leanh::lean_ctor_get(v_stx_3537_, 1);
                                v_args_3616_ = leanh::lean_ctor_get(v_stx_3537_, 2);
                                v_isSharedCheck_3644_ =
                                    (!leanh::lean_is_exclusive(v_stx_3537_)) as u8;
                                if v_isSharedCheck_3644_ == 0 {
                                    v___x_3618_ = v_stx_3537_;
                                    v_isShared_3619_ = v_isSharedCheck_3644_;
                                    state = 13;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_args_3616_);
                                    leanh::lean_inc(v_kind_3615_);
                                    leanh::lean_inc(v_info_3614_);
                                    leanh::lean_dec(v_stx_3537_);
                                    v___x_3618_ = leanh::lean_box(0);
                                    v_isShared_3619_ = v_isSharedCheck_3644_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v___x_3645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_3645_, 0, v_stx_3537_);
                                leanh::lean_ctor_set(v___x_3645_, 1, v_a_3539_);
                                return v___x_3645_;
                            }
                        } else {
                            v_e_3646_ = l_Lean_Syntax_getArg(v_stx_3537_, v___x_3610_);
                            v___x_3647_ = l_Lean_TSyntax_getHygieneInfo(v_h_3611_);
                            leanh::lean_dec(v_h_3611_);
                            v___x_3648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_3648_, 0, v___x_3647_);
                            leanh::lean_inc(v_e_3646_);
                            v___x_3649_ = l_Lean_Elab_Term_expandCDot_x3f(
                                v_e_3646_,
                                v___x_3648_,
                                v_a_3538_,
                                v_a_3539_,
                            );
                            leanh::lean_dec_ref_known(v___x_3648_, 1);
                            if leanh::lean_obj_tag(v___x_3649_) == 0 {
                                v_a_3650_ = leanh::lean_ctor_get(v___x_3649_, 0);
                                leanh::lean_inc(v_a_3650_);
                                v_a_3651_ = leanh::lean_ctor_get(v___x_3649_, 1);
                                leanh::lean_inc(v_a_3651_);
                                leanh::lean_dec_ref_known(v___x_3649_, 2);
                                if leanh::lean_obj_tag(v_a_3650_) == 0 {
                                    v___y_3653_ = v_e_3646_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_e_3646_);
                                    v_val_3665_ = leanh::lean_ctor_get(v_a_3650_, 0);
                                    leanh::lean_inc(v_val_3665_);
                                    leanh::lean_dec_ref_known(v_a_3650_, 1);
                                    v___y_3653_ = v_val_3665_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_e_3646_);
                                leanh::lean_dec(v_stx_3537_);
                                v_a_3666_ = leanh::lean_ctor_get(v___x_3649_, 0);
                                v_a_3667_ = leanh::lean_ctor_get(v___x_3649_, 1);
                                v_isSharedCheck_3674_ =
                                    (!leanh::lean_is_exclusive(v___x_3649_)) as u8;
                                if v_isSharedCheck_3674_ == 0 {
                                    v___x_3669_ = v___x_3649_;
                                    v_isShared_3670_ = v_isSharedCheck_3674_;
                                    state = 22;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_3667_);
                                    leanh::lean_inc(v_a_3666_);
                                    leanh::lean_dec(v___x_3649_);
                                    v___x_3669_ = leanh::lean_box(0);
                                    v_isShared_3670_ = v_isSharedCheck_3674_;
                                    state = 22;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v_sz_3548_ = lean_array_size(v_args_3544_);
                v___x_3549_ = 0usize;
                v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_3548_, v___x_3549_, v_args_3544_, v_a_3538_, v_a_3539_);
                if leanh::lean_obj_tag(v___x_3550_) == 0 {
                    v_a_3551_ = leanh::lean_ctor_get(v___x_3550_, 0);
                    v_a_3552_ = leanh::lean_ctor_get(v___x_3550_, 1);
                    v_isSharedCheck_3562_ = (!leanh::lean_is_exclusive(v___x_3550_)) as u8;
                    if v_isSharedCheck_3562_ == 0 {
                        v___x_3554_ = v___x_3550_;
                        v_isShared_3555_ = v_isSharedCheck_3562_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3552_);
                        leanh::lean_inc(v_a_3551_);
                        leanh::lean_dec(v___x_3550_);
                        v___x_3554_ = leanh::lean_box(0);
                        v_isShared_3555_ = v_isSharedCheck_3562_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3546_);
                    leanh::lean_dec(v_kind_3543_);
                    leanh::lean_dec(v_info_3542_);
                    v_a_3563_ = leanh::lean_ctor_get(v___x_3550_, 0);
                    v_a_3564_ = leanh::lean_ctor_get(v___x_3550_, 1);
                    v_isSharedCheck_3571_ = (!leanh::lean_is_exclusive(v___x_3550_)) as u8;
                    if v_isSharedCheck_3571_ == 0 {
                        v___x_3566_ = v___x_3550_;
                        v_isShared_3567_ = v_isSharedCheck_3571_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3564_);
                        leanh::lean_inc(v_a_3563_);
                        leanh::lean_dec(v___x_3550_);
                        v___x_3566_ = leanh::lean_box(0);
                        v_isShared_3567_ = v_isSharedCheck_3571_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3547_ == 0 {
                    leanh::lean_ctor_set(v___x_3546_, 2, v_a_3551_);
                    v___x_3557_ = v___x_3546_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3561_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_info_3542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 1, v_kind_3543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 2, v_a_3551_);
                    v___x_3557_ = v_reuseFailAlloc_3561_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3555_ == 0 {
                    leanh::lean_ctor_set(v___x_3554_, 0, v___x_3557_);
                    v___x_3559_ = v___x_3554_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3560_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3557_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_a_3552_);
                    v___x_3559_ = v_reuseFailAlloc_3560_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3559_;
            }
            5 => {
                if v_isShared_3567_ == 0 {
                    v___x_3569_ = v___x_3566_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3570_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3570_, 1, v_a_3564_);
                    v___x_3569_ = v_reuseFailAlloc_3570_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3569_;
            }
            7 => {
                v_sz_3584_ = lean_array_size(v_args_3580_);
                v___x_3585_ = 0usize;
                v___x_3586_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_3584_, v___x_3585_, v_args_3580_, v_a_3538_, v_a_3539_);
                if leanh::lean_obj_tag(v___x_3586_) == 0 {
                    v_a_3587_ = leanh::lean_ctor_get(v___x_3586_, 0);
                    v_a_3588_ = leanh::lean_ctor_get(v___x_3586_, 1);
                    v_isSharedCheck_3598_ = (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                    if v_isSharedCheck_3598_ == 0 {
                        v___x_3590_ = v___x_3586_;
                        v_isShared_3591_ = v_isSharedCheck_3598_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3588_);
                        leanh::lean_inc(v_a_3587_);
                        leanh::lean_dec(v___x_3586_);
                        v___x_3590_ = leanh::lean_box(0);
                        v_isShared_3591_ = v_isSharedCheck_3598_;
                        state = 8;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3582_);
                    leanh::lean_dec(v_kind_3579_);
                    leanh::lean_dec(v_info_3578_);
                    v_a_3599_ = leanh::lean_ctor_get(v___x_3586_, 0);
                    v_a_3600_ = leanh::lean_ctor_get(v___x_3586_, 1);
                    v_isSharedCheck_3607_ = (!leanh::lean_is_exclusive(v___x_3586_)) as u8;
                    if v_isSharedCheck_3607_ == 0 {
                        v___x_3602_ = v___x_3586_;
                        v_isShared_3603_ = v_isSharedCheck_3607_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3600_);
                        leanh::lean_inc(v_a_3599_);
                        leanh::lean_dec(v___x_3586_);
                        v___x_3602_ = leanh::lean_box(0);
                        v_isShared_3603_ = v_isSharedCheck_3607_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_3583_ == 0 {
                    leanh::lean_ctor_set(v___x_3582_, 2, v_a_3587_);
                    v___x_3593_ = v___x_3582_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3597_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_info_3578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_kind_3579_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3597_, 2, v_a_3587_);
                    v___x_3593_ = v_reuseFailAlloc_3597_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_3591_ == 0 {
                    leanh::lean_ctor_set(v___x_3590_, 0, v___x_3593_);
                    v___x_3595_ = v___x_3590_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3596_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 0, v___x_3593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3596_, 1, v_a_3588_);
                    v___x_3595_ = v_reuseFailAlloc_3596_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3595_;
            }
            11 => {
                if v_isShared_3603_ == 0 {
                    v___x_3605_ = v___x_3602_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3606_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3606_, 1, v_a_3600_);
                    v___x_3605_ = v_reuseFailAlloc_3606_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3605_;
            }
            13 => {
                v_sz_3620_ = lean_array_size(v_args_3616_);
                v___x_3621_ = 0usize;
                v___x_3622_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_3620_, v___x_3621_, v_args_3616_, v_a_3538_, v_a_3539_);
                if leanh::lean_obj_tag(v___x_3622_) == 0 {
                    v_a_3623_ = leanh::lean_ctor_get(v___x_3622_, 0);
                    v_a_3624_ = leanh::lean_ctor_get(v___x_3622_, 1);
                    v_isSharedCheck_3634_ = (!leanh::lean_is_exclusive(v___x_3622_)) as u8;
                    if v_isSharedCheck_3634_ == 0 {
                        v___x_3626_ = v___x_3622_;
                        v_isShared_3627_ = v_isSharedCheck_3634_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3624_);
                        leanh::lean_inc(v_a_3623_);
                        leanh::lean_dec(v___x_3622_);
                        v___x_3626_ = leanh::lean_box(0);
                        v_isShared_3627_ = v_isSharedCheck_3634_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3618_);
                    leanh::lean_dec(v_kind_3615_);
                    leanh::lean_dec(v_info_3614_);
                    v_a_3635_ = leanh::lean_ctor_get(v___x_3622_, 0);
                    v_a_3636_ = leanh::lean_ctor_get(v___x_3622_, 1);
                    v_isSharedCheck_3643_ = (!leanh::lean_is_exclusive(v___x_3622_)) as u8;
                    if v_isSharedCheck_3643_ == 0 {
                        v___x_3638_ = v___x_3622_;
                        v_isShared_3639_ = v_isSharedCheck_3643_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3636_);
                        leanh::lean_inc(v_a_3635_);
                        leanh::lean_dec(v___x_3622_);
                        v___x_3638_ = leanh::lean_box(0);
                        v_isShared_3639_ = v_isSharedCheck_3643_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3619_ == 0 {
                    leanh::lean_ctor_set(v___x_3618_, 2, v_a_3623_);
                    v___x_3629_ = v___x_3618_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3633_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_info_3614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 1, v_kind_3615_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 2, v_a_3623_);
                    v___x_3629_ = v_reuseFailAlloc_3633_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3627_ == 0 {
                    leanh::lean_ctor_set(v___x_3626_, 0, v___x_3629_);
                    v___x_3631_ = v___x_3626_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3632_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 0, v___x_3629_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3632_, 1, v_a_3624_);
                    v___x_3631_ = v_reuseFailAlloc_3632_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3631_;
            }
            17 => {
                if v_isShared_3639_ == 0 {
                    v___x_3641_ = v___x_3638_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3642_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3635_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_a_3636_);
                    v___x_3641_ = v_reuseFailAlloc_3642_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3641_;
            }
            19 => {
                v___x_3654_ =
                    l_Lean_Elab_Command_removeParentheses(v___y_3653_, v_a_3538_, v_a_3651_);
                if leanh::lean_obj_tag(v___x_3654_) == 0 {
                    v_a_3655_ = leanh::lean_ctor_get(v___x_3654_, 0);
                    v_a_3656_ = leanh::lean_ctor_get(v___x_3654_, 1);
                    v_isSharedCheck_3664_ = (!leanh::lean_is_exclusive(v___x_3654_)) as u8;
                    if v_isSharedCheck_3664_ == 0 {
                        v___x_3658_ = v___x_3654_;
                        v_isShared_3659_ = v_isSharedCheck_3664_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3656_);
                        leanh::lean_inc(v_a_3655_);
                        leanh::lean_dec(v___x_3654_);
                        v___x_3658_ = leanh::lean_box(0);
                        v_isShared_3659_ = v_isSharedCheck_3664_;
                        state = 20;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_stx_3537_);
                    return v___x_3654_;
                }
            }
            20 => {
                v___x_3660_ = l_Lean_Elab_Command_removeParenthesesAux(v_stx_3537_, v_a_3655_);
                leanh::lean_dec(v_stx_3537_);
                if v_isShared_3659_ == 0 {
                    leanh::lean_ctor_set(v___x_3658_, 0, v___x_3660_);
                    v___x_3662_ = v___x_3658_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v_a_3656_);
                    v___x_3662_ = v_reuseFailAlloc_3663_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3662_;
            }
            22 => {
                if v_isShared_3670_ == 0 {
                    v___x_3672_ = v___x_3669_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3673_, 1, v_a_3667_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3672_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(
    mut v_sz_3675_: usize,
    mut v_i_3676_: usize,
    mut v_bs_3677_: *mut leanh::LeanObject,
    mut v___y_3678_: *mut leanh::LeanObject,
    mut v___y_3679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3680_: u8 = 0;
    let mut v___x_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: usize = 0;
    let mut v___x_3689_: usize = 0;
    let mut v___x_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3680_ = lean_usize_dec_lt(v_i_3676_, v_sz_3675_);
                if v___x_3680_ == 0 {
                    v___x_3681_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3681_, 0, v_bs_3677_);
                    leanh::lean_ctor_set(v___x_3681_, 1, v___y_3679_);
                    return v___x_3681_;
                } else {
                    v_v_3682_ = lean_array_uget_borrowed(v_bs_3677_, v_i_3676_);
                    leanh::lean_inc(v_v_3682_);
                    v___x_3683_ =
                        l_Lean_Elab_Command_removeParentheses(v_v_3682_, v___y_3678_, v___y_3679_);
                    if leanh::lean_obj_tag(v___x_3683_) == 0 {
                        v_a_3684_ = leanh::lean_ctor_get(v___x_3683_, 0);
                        leanh::lean_inc(v_a_3684_);
                        v_a_3685_ = leanh::lean_ctor_get(v___x_3683_, 1);
                        leanh::lean_inc(v_a_3685_);
                        leanh::lean_dec_ref_known(v___x_3683_, 2);
                        v___x_3686_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3687_ = lean_array_uset(v_bs_3677_, v_i_3676_, v___x_3686_);
                        v___x_3688_ = 1usize;
                        v___x_3689_ = lean_usize_add(v_i_3676_, v___x_3688_);
                        v___x_3690_ = lean_array_uset(v_bs_x27_3687_, v_i_3676_, v_a_3684_);
                        v_i_3676_ = v___x_3689_;
                        v_bs_3677_ = v___x_3690_;
                        v___y_3679_ = v_a_3685_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_3677_);
                        v_a_3692_ = leanh::lean_ctor_get(v___x_3683_, 0);
                        v_a_3693_ = leanh::lean_ctor_get(v___x_3683_, 1);
                        v_isSharedCheck_3700_ =
                            (!leanh::lean_is_exclusive(v___x_3683_)) as u8;
                        if v_isSharedCheck_3700_ == 0 {
                            v___x_3695_ = v___x_3683_;
                            v_isShared_3696_ = v_isSharedCheck_3700_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3693_);
                            leanh::lean_inc(v_a_3692_);
                            leanh::lean_dec(v___x_3683_);
                            v___x_3695_ = leanh::lean_box(0);
                            v_isShared_3696_ = v_isSharedCheck_3700_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3696_ == 0 {
                    v___x_3698_ = v___x_3695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3692_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 1, v_a_3693_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0___boxed(
    mut v_sz_3701_: *mut leanh::LeanObject,
    mut v_i_3702_: *mut leanh::LeanObject,
    mut v_bs_3703_: *mut leanh::LeanObject,
    mut v___y_3704_: *mut leanh::LeanObject,
    mut v___y_3705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3706_: usize = 0;
    let mut v_i_boxed_3707_: usize = 0;
    let mut v_res_3708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3706_ = leanh::lean_unbox_usize(v_sz_3701_);
    leanh::lean_dec(v_sz_3701_);
    v_i_boxed_3707_ = leanh::lean_unbox_usize(v_i_3702_);
    leanh::lean_dec(v_i_3702_);
    v_res_3708_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_boxed_3706_, v_i_boxed_3707_, v_bs_3703_, v___y_3704_, v___y_3705_);
    leanh::lean_dec_ref(v___y_3704_);
    return v_res_3708_;
}
pub unsafe fn l_Lean_Elab_Command_removeParentheses___boxed(
    mut v_stx_3709_: *mut leanh::LeanObject,
    mut v_a_3710_: *mut leanh::LeanObject,
    mut v_a_3711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3712_ = l_Lean_Elab_Command_removeParentheses(v_stx_3709_, v_a_3710_, v_a_3711_);
    leanh::lean_dec_ref(v_a_3710_);
    return v_res_3712_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(
    mut v___x_3716_: *mut leanh::LeanObject,
    mut v_firstChoiceOnly_3717_: u8,
    mut v_stx_3718_: *mut leanh::LeanObject,
    mut v_b_3719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3725_: usize = 0;
    let mut v___x_3726_: usize = 0;
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: u8 = 0;
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: u8 = 0;
    let mut v___x_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3768_: u8 = 0;
    let mut v_unused_3769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3744_ = leanh::lean_ctor_get(v_b_3719_, 1);
                v_isSharedCheck_3768_ = (!leanh::lean_is_exclusive(v_b_3719_)) as u8;
                if v_isSharedCheck_3768_ == 0 {
                    v_unused_3769_ = leanh::lean_ctor_get(v_b_3719_, 0);
                    leanh::lean_dec(v_unused_3769_);
                    v___x_3746_ = v_b_3719_;
                    v_isShared_3747_ = v_isSharedCheck_3768_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3744_);
                    leanh::lean_dec(v_b_3719_);
                    v___x_3746_ = leanh::lean_box(0);
                    v_isShared_3747_ = v_isSharedCheck_3768_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3723_ = leanh::lean_box(0);
                v___x_3724_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3724_, 0, v___x_3723_);
                leanh::lean_ctor_set(v___x_3724_, 1, v___y_3722_);
                v_sz_3725_ = lean_array_size(v___y_3721_);
                v___x_3726_ = 0usize;
                v___x_3727_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_3716_, v_firstChoiceOnly_3717_, v___y_3721_, v_sz_3725_, v___x_3726_, v___x_3724_);
                v_fst_3728_ = leanh::lean_ctor_get(v___x_3727_, 0);
                leanh::lean_inc(v_fst_3728_);
                if leanh::lean_obj_tag(v_fst_3728_) == 0 {
                    v_snd_3729_ = leanh::lean_ctor_get(v___x_3727_, 1);
                    leanh::lean_inc(v_snd_3729_);
                    leanh::lean_dec_ref(v___x_3727_);
                    v___x_3730_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3730_, 0, v_snd_3729_);
                    return v___x_3730_;
                } else {
                    leanh::lean_dec_ref(v___x_3727_);
                    v_val_3731_ = leanh::lean_ctor_get(v_fst_3728_, 0);
                    leanh::lean_inc(v_val_3731_);
                    leanh::lean_dec_ref_known(v_fst_3728_, 1);
                    return v_val_3731_;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_stx_3718_) == 1 {
                    leanh::lean_dec_ref(v___y_3733_);
                    if v_firstChoiceOnly_3717_ == 0 {
                        v_args_3735_ = leanh::lean_ctor_get(v_stx_3718_, 2);
                        v___y_3721_ = v_args_3735_;
                        v___y_3722_ = v_a_3734_;
                        state = 1;
                        continue;
                    } else {
                        v_kind_3736_ = leanh::lean_ctor_get(v_stx_3718_, 1);
                        v_args_3737_ = leanh::lean_ctor_get(v_stx_3718_, 2);
                        v___x_3738_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___closed__1;
                        v___x_3739_ = lean_name_eq(v_kind_3736_, v___x_3738_);
                        if v___x_3739_ == 0 {
                            v___y_3721_ = v_args_3737_;
                            v___y_3722_ = v_a_3734_;
                            state = 1;
                            continue;
                        } else {
                            v___x_3740_ = leanh::lean_box(0);
                            v___x_3741_ = leanh::lean_unsigned_to_nat(0);
                            v___x_3742_ =
                                lean_array_get_borrowed(v___x_3740_, v_args_3737_, v___x_3741_);
                            v_stx_3718_ = v___x_3742_;
                            v_b_3719_ = v_a_3734_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_a_3734_);
                    return v___y_3733_;
                }
            }
            3 => {
                v___x_3748_ = leanh::lean_box(0);
                v___x_3749_ = l_Lean_Syntax_isAntiquot(v_stx_3718_);
                if v___x_3749_ == 0 {
                    if v_isShared_3747_ == 0 {
                        leanh::lean_ctor_set(v___x_3746_, 0, v___x_3748_);
                        v___x_3751_ = v___x_3746_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3753_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 0, v___x_3748_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_snd_3744_);
                        v___x_3751_ = v_reuseFailAlloc_3753_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_3754_ = l_Lean_Syntax_getAntiquotTerm(v_stx_3718_);
                    v___x_3755_ = l_Lean_Syntax_getId(v___x_3754_);
                    leanh::lean_dec(v___x_3754_);
                    v___x_3756_ = l_Lean_NameSet_contains(v_snd_3744_, v___x_3755_);
                    if v___x_3756_ == 0 {
                        v___x_3757_ = l_Lean_NameSet_insert(v_snd_3744_, v___x_3755_);
                        if v_isShared_3747_ == 0 {
                            leanh::lean_ctor_set(v___x_3746_, 1, v___x_3757_);
                            leanh::lean_ctor_set(v___x_3746_, 0, v___x_3748_);
                            v___x_3759_ = v___x_3746_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_3761_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v___x_3748_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 1, v___x_3757_);
                            v___x_3759_ = v_reuseFailAlloc_3761_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_3755_);
                        v___x_3762_ = leanh::lean_box((v___x_3756_) as usize);
                        v___x_3763_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3763_, 0, v___x_3762_);
                        if v_isShared_3747_ == 0 {
                            leanh::lean_ctor_set(v___x_3746_, 0, v___x_3763_);
                            v___x_3765_ = v___x_3746_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3767_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3763_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3767_, 1, v_snd_3744_);
                            v___x_3765_ = v_reuseFailAlloc_3767_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            4 => {
                leanh::lean_inc_ref(v___x_3751_);
                v___x_3752_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3752_, 0, v___x_3751_);
                v___y_3733_ = v___x_3752_;
                v_a_3734_ = v___x_3751_;
                state = 2;
                continue;
            }
            5 => {
                leanh::lean_inc_ref(v___x_3759_);
                v___x_3760_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3760_, 0, v___x_3759_);
                v___y_3733_ = v___x_3760_;
                v_a_3734_ = v___x_3759_;
                state = 2;
                continue;
            }
            6 => {
                v___x_3766_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3766_, 0, v___x_3765_);
                return v___x_3766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(
    mut v___x_3770_: *mut leanh::LeanObject,
    mut v_firstChoiceOnly_3771_: u8,
    mut v_as_3772_: *mut leanh::LeanObject,
    mut v_sz_3773_: usize,
    mut v_i_3774_: usize,
    mut v_b_3775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3776_: u8 = 0;
    let mut v_snd_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3780_: u8 = 0;
    let mut v_a_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: usize = 0;
    let mut v___x_3792_: usize = 0;
    let mut v_reuseFailAlloc_3794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut v_unused_3796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3776_ = lean_usize_dec_lt(v_i_3774_, v_sz_3773_);
                if v___x_3776_ == 0 {
                    return v_b_3775_;
                } else {
                    v_snd_3777_ = leanh::lean_ctor_get(v_b_3775_, 1);
                    v_isSharedCheck_3795_ = (!leanh::lean_is_exclusive(v_b_3775_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v_unused_3796_ = leanh::lean_ctor_get(v_b_3775_, 0);
                        leanh::lean_dec(v_unused_3796_);
                        v___x_3779_ = v_b_3775_;
                        v_isShared_3780_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3777_);
                        leanh::lean_dec(v_b_3775_);
                        v___x_3779_ = leanh::lean_box(0);
                        v_isShared_3780_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3781_ = lean_array_uget_borrowed(v_as_3772_, v_i_3774_);
                leanh::lean_inc(v_snd_3777_);
                v___x_3782_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_3770_, v_firstChoiceOnly_3771_, v_a_3781_, v_snd_3777_);
                if leanh::lean_obj_tag(v___x_3782_) == 0 {
                    v___x_3783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3783_, 0, v___x_3782_);
                    if v_isShared_3780_ == 0 {
                        leanh::lean_ctor_set(v___x_3779_, 0, v___x_3783_);
                        v___x_3785_ = v___x_3779_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3786_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3783_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3786_, 1, v_snd_3777_);
                        v___x_3785_ = v_reuseFailAlloc_3786_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_3777_);
                    v_a_3787_ = leanh::lean_ctor_get(v___x_3782_, 0);
                    leanh::lean_inc(v_a_3787_);
                    leanh::lean_dec_ref_known(v___x_3782_, 1);
                    v___x_3788_ = leanh::lean_box(0);
                    if v_isShared_3780_ == 0 {
                        leanh::lean_ctor_set(v___x_3779_, 1, v_a_3787_);
                        leanh::lean_ctor_set(v___x_3779_, 0, v___x_3788_);
                        v___x_3790_ = v___x_3779_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3794_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 0, v___x_3788_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3794_, 1, v_a_3787_);
                        v___x_3790_ = v_reuseFailAlloc_3794_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3785_;
            }
            3 => {
                v___x_3791_ = 1usize;
                v___x_3792_ = lean_usize_add(v_i_3774_, v___x_3791_);
                v_i_3774_ = v___x_3792_;
                v_b_3775_ = v___x_3790_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0___boxed(
    mut v___x_3797_: *mut leanh::LeanObject,
    mut v_firstChoiceOnly_3798_: *mut leanh::LeanObject,
    mut v_as_3799_: *mut leanh::LeanObject,
    mut v_sz_3800_: *mut leanh::LeanObject,
    mut v_i_3801_: *mut leanh::LeanObject,
    mut v_b_3802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_3803_: u8 = 0;
    let mut v_sz_boxed_3804_: usize = 0;
    let mut v_i_boxed_3805_: usize = 0;
    let mut v_res_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_3803_ = (leanh::lean_unbox(v_firstChoiceOnly_3798_) as u8);
    v_sz_boxed_3804_ = leanh::lean_unbox_usize(v_sz_3800_);
    leanh::lean_dec(v_sz_3800_);
    v_i_boxed_3805_ = leanh::lean_unbox_usize(v_i_3801_);
    leanh::lean_dec(v_i_3801_);
    v_res_3806_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0_spec__0(v___x_3797_, v_firstChoiceOnly_boxed_3803_, v_as_3799_, v_sz_boxed_3804_, v_i_boxed_3805_, v_b_3802_);
    leanh::lean_dec_ref(v_as_3799_);
    leanh::lean_dec_ref(v___x_3797_);
    return v_res_3806_;
}
pub unsafe fn l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0___boxed(
    mut v___x_3807_: *mut leanh::LeanObject,
    mut v_firstChoiceOnly_3808_: *mut leanh::LeanObject,
    mut v_stx_3809_: *mut leanh::LeanObject,
    mut v_b_3810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_firstChoiceOnly_boxed_3811_: u8 = 0;
    let mut v_res_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_firstChoiceOnly_boxed_3811_ = (leanh::lean_unbox(v_firstChoiceOnly_3808_) as u8);
    v_res_3812_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_3807_, v_firstChoiceOnly_boxed_3811_, v_stx_3809_, v_b_3810_);
    leanh::lean_dec(v_stx_3809_);
    leanh::lean_dec_ref(v___x_3807_);
    return v_res_3812_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(
    mut v_as_3813_: *mut leanh::LeanObject,
    mut v_sz_3814_: usize,
    mut v_i_3815_: usize,
    mut v_b_3816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3817_: u8 = 0;
    let mut v_snd_3818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3821_: u8 = 0;
    let mut v_a_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_firstChoiceOnly_3824_: u8 = 0;
    let mut v_stx_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3833_: u8 = 0;
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: usize = 0;
    let mut v___x_3837_: usize = 0;
    let mut v_reuseFailAlloc_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3840_: u8 = 0;
    let mut v_unused_3841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v___x_3847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3849_: u8 = 0;
    let mut v_unused_3850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3856_: u8 = 0;
    let mut v_unused_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3817_ = lean_usize_dec_lt(v_i_3815_, v_sz_3814_);
                if v___x_3817_ == 0 {
                    return v_b_3816_;
                } else {
                    v_snd_3818_ = leanh::lean_ctor_get(v_b_3816_, 1);
                    v_isSharedCheck_3856_ = (!leanh::lean_is_exclusive(v_b_3816_)) as u8;
                    if v_isSharedCheck_3856_ == 0 {
                        v_unused_3857_ = leanh::lean_ctor_get(v_b_3816_, 0);
                        leanh::lean_dec(v_unused_3857_);
                        v___x_3820_ = v_b_3816_;
                        v_isShared_3821_ = v_isSharedCheck_3856_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3818_);
                        leanh::lean_dec(v_b_3816_);
                        v___x_3820_ = leanh::lean_box(0);
                        v_isShared_3821_ = v_isSharedCheck_3856_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3822_ = lean_array_uget_borrowed(v_as_3813_, v_i_3815_);
                leanh::lean_inc(v_a_3822_);
                v___x_3823_ = l_Lean_Syntax_topDown(v_a_3822_, v___x_3817_);
                v_firstChoiceOnly_3824_ = leanh::lean_ctor_get_uint8(
                    v___x_3823_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_stx_3825_ = leanh::lean_ctor_get(v___x_3823_, 0);
                leanh::lean_inc(v_stx_3825_);
                leanh::lean_dec_ref(v___x_3823_);
                v___x_3826_ = leanh::lean_box(0);
                if v_isShared_3821_ == 0 {
                    leanh::lean_ctor_set(v___x_3820_, 0, v___x_3826_);
                    v___x_3852_ = v___x_3820_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3855_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 0, v___x_3826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3855_, 1, v_snd_3818_);
                    v___x_3852_ = v_reuseFailAlloc_3855_;
                    state = 7;
                    continue;
                }
            }
            2 => {
                v_fst_3829_ = leanh::lean_ctor_get(v___y_3828_, 0);
                if leanh::lean_obj_tag(v_fst_3829_) == 0 {
                    v_snd_3830_ = leanh::lean_ctor_get(v___y_3828_, 1);
                    v_isSharedCheck_3840_ = (!leanh::lean_is_exclusive(v___y_3828_)) as u8;
                    if v_isSharedCheck_3840_ == 0 {
                        v_unused_3841_ = leanh::lean_ctor_get(v___y_3828_, 0);
                        leanh::lean_dec(v_unused_3841_);
                        v___x_3832_ = v___y_3828_;
                        v_isShared_3833_ = v_isSharedCheck_3840_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3830_);
                        leanh::lean_dec(v___y_3828_);
                        v___x_3832_ = leanh::lean_box(0);
                        v_isShared_3833_ = v_isSharedCheck_3840_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_3829_);
                    v_snd_3842_ = leanh::lean_ctor_get(v___y_3828_, 1);
                    v_isSharedCheck_3849_ = (!leanh::lean_is_exclusive(v___y_3828_)) as u8;
                    if v_isSharedCheck_3849_ == 0 {
                        v_unused_3850_ = leanh::lean_ctor_get(v___y_3828_, 0);
                        leanh::lean_dec(v_unused_3850_);
                        v___x_3844_ = v___y_3828_;
                        v_isShared_3845_ = v_isSharedCheck_3849_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3842_);
                        leanh::lean_dec(v___y_3828_);
                        v___x_3844_ = leanh::lean_box(0);
                        v_isShared_3845_ = v_isSharedCheck_3849_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3833_ == 0 {
                    leanh::lean_ctor_set(v___x_3832_, 0, v___x_3826_);
                    v___x_3835_ = v___x_3832_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3839_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3826_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3839_, 1, v_snd_3830_);
                    v___x_3835_ = v_reuseFailAlloc_3839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3836_ = 1usize;
                v___x_3837_ = lean_usize_add(v_i_3815_, v___x_3836_);
                v_i_3815_ = v___x_3837_;
                v_b_3816_ = v___x_3835_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3845_ == 0 {
                    v___x_3847_ = v___x_3844_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3848_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_fst_3829_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_snd_3842_);
                    v___x_3847_ = v_reuseFailAlloc_3848_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3847_;
            }
            7 => {
                leanh::lean_inc_ref(v___x_3852_);
                v___x_3853_ = l_Lean_Syntax_instForInTopDownOfMonad_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__0(v___x_3852_, v_firstChoiceOnly_3824_, v_stx_3825_, v___x_3852_);
                leanh::lean_dec(v_stx_3825_);
                leanh::lean_dec_ref(v___x_3852_);
                v_a_3854_ = leanh::lean_ctor_get(v___x_3853_, 0);
                leanh::lean_inc(v_a_3854_);
                leanh::lean_dec_ref(v___x_3853_);
                v___y_3828_ = v_a_3854_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1___boxed(
    mut v_as_3858_: *mut leanh::LeanObject,
    mut v_sz_3859_: *mut leanh::LeanObject,
    mut v_i_3860_: *mut leanh::LeanObject,
    mut v_b_3861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_3862_: usize = 0;
    let mut v_i_boxed_3863_: usize = 0;
    let mut v_res_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3862_ = leanh::lean_unbox_usize(v_sz_3859_);
    leanh::lean_dec(v_sz_3859_);
    v_i_boxed_3863_ = leanh::lean_unbox_usize(v_i_3860_);
    leanh::lean_dec(v_i_3860_);
    v_res_3864_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_as_3858_, v_sz_boxed_3862_, v_i_boxed_3863_, v_b_3861_);
    leanh::lean_dec_ref(v_as_3858_);
    return v_res_3864_;
}
pub unsafe fn _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0()
-> *mut leanh::LeanObject {
    let mut v_seen_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_seen_3865_ = l_Lean_NameSet_empty;
    v___x_3866_ = leanh::lean_box(0);
    v___x_3867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3867_, 0, v___x_3866_);
    leanh::lean_ctor_set(v___x_3867_, 1, v_seen_3865_);
    return v___x_3867_;
}
pub unsafe fn l_Lean_Elab_Command_hasDuplicateAntiquot(
    mut v_stxs_3868_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3870_: usize = 0;
    let mut v___x_3871_: usize = 0;
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3869_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0_once),
        _init_l_Lean_Elab_Command_hasDuplicateAntiquot___closed__0,
    );
    v_sz_3870_ = lean_array_size(v_stxs_3868_);
    v___x_3871_ = 0usize;
    v___x_3872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_hasDuplicateAntiquot_spec__1(v_stxs_3868_, v_sz_3870_, v___x_3871_, v___x_3869_);
    v_fst_3873_ = leanh::lean_ctor_get(v___x_3872_, 0);
    leanh::lean_inc(v_fst_3873_);
    leanh::lean_dec_ref(v___x_3872_);
    if leanh::lean_obj_tag(v_fst_3873_) == 0 {
        let mut v___x_3874_: u8 = 0;
        v___x_3874_ = 0;
        return v___x_3874_;
    } else {
        let mut v_val_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3876_: u8 = 0;
        v_val_3875_ = leanh::lean_ctor_get(v_fst_3873_, 0);
        leanh::lean_inc(v_val_3875_);
        leanh::lean_dec_ref_known(v_fst_3873_, 1);
        v___x_3876_ = (leanh::lean_unbox(v_val_3875_) as u8);
        leanh::lean_dec(v_val_3875_);
        return v___x_3876_;
    }
}
pub unsafe fn l_Lean_Elab_Command_hasDuplicateAntiquot___boxed(
    mut v_stxs_3877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3878_: u8 = 0;
    let mut v_r_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3878_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_stxs_3877_);
    leanh::lean_dec_ref(v_stxs_3877_);
    v_r_3879_ = leanh::lean_box((v_res_3878_) as usize);
    return v_r_3879_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3886_ = l_Lean_Elab_Command_mkUnexpander___closed__3;
    v___x_3887_ = l_String_toRawSubstring_x27(v___x_3886_);
    return v___x_3887_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__15() -> *mut leanh::LeanObject
{
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3908_ = l_Lean_Elab_Command_mkUnexpander___closed__14;
    v___x_3909_ = l_String_toRawSubstring_x27(v___x_3908_);
    return v___x_3909_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__19() -> *mut leanh::LeanObject
{
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Lean_Elab_Command_mkUnexpander___closed__18;
    v___x_3915_ = l_String_toRawSubstring_x27(v___x_3914_);
    return v___x_3915_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__22() -> *mut leanh::LeanObject
{
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = l_Lean_Elab_Command_mkUnexpander___closed__21;
    v___x_3920_ = l_String_toRawSubstring_x27(v___x_3919_);
    return v___x_3920_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__40() -> *mut leanh::LeanObject
{
    let mut v___x_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_Elab_Command_mkUnexpander___closed__39;
    v___x_3958_ = l_String_toRawSubstring_x27(v___x_3957_);
    return v___x_3958_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__47() -> *mut leanh::LeanObject
{
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = l_Lean_Elab_Command_mkUnexpander___closed__46;
    v___x_3973_ = l_String_toRawSubstring_x27(v___x_3972_);
    return v___x_3973_;
}
pub unsafe fn _init_l_Lean_Elab_Command_mkUnexpander___closed__55() -> *mut leanh::LeanObject
{
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_Elab_Command_mkUnexpander___closed__54;
    v___x_3989_ = l_String_toRawSubstring_x27(v___x_3988_);
    return v___x_3989_;
}
pub unsafe fn l_Lean_Elab_Command_mkUnexpander(
    mut v_attrKind_4027_: *mut leanh::LeanObject,
    mut v_pat_4028_: *mut leanh::LeanObject,
    mut v_qrhs_4029_: *mut leanh::LeanObject,
    mut v_a_4030_: *mut leanh::LeanObject,
    mut v_a_4031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4049_: u8 = 0;
    let mut v_a_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4054_: u8 = 0;
    let mut v_sz_4055_: usize = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4062_: u8 = 0;
    let mut v___x_4063_: u8 = 0;
    let mut v_quotContext_4064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4207_: u8 = 0;
    let mut v_a_4208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4216_: u8 = 0;
    let mut v_isSharedCheck_4217_: u8 = 0;
    let mut v_unused_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_unused_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4228_: u8 = 0;
    let mut v___x_4230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4232_: u8 = 0;
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: u8 = 0;
    let mut v___x_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4233_ = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
                leanh::lean_inc(v_qrhs_4029_);
                v___x_4234_ = l_Lean_Syntax_isOfKind(v_qrhs_4029_, v___x_4233_);
                if v___x_4234_ == 0 {
                    v___x_4235_ =
                        l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                    leanh::lean_inc(v_qrhs_4029_);
                    v___x_4236_ = l_Lean_Syntax_isOfKind(v_qrhs_4029_, v___x_4235_);
                    if v___x_4236_ == 0 {
                        leanh::lean_dec(v_qrhs_4029_);
                        leanh::lean_dec(v_pat_4028_);
                        leanh::lean_dec(v_attrKind_4027_);
                        v___x_4237_ = leanh::lean_box(0);
                        v___x_4238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4238_, 0, v___x_4237_);
                        leanh::lean_ctor_set(v___x_4238_, 1, v_a_4031_);
                        return v___x_4238_;
                    } else {
                        v___x_4239_ = l_Lean_Elab_Command_mkUnexpander___closed__68;
                        v_fst_4037_ = v_qrhs_4029_;
                        v_snd_4038_ = v___x_4239_;
                        v___y_4039_ = v_a_4030_;
                        v___y_4040_ = v_a_4031_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4240_ = leanh::lean_unsigned_to_nat(0);
                    v_c_4241_ = l_Lean_Syntax_getArg(v_qrhs_4029_, v___x_4240_);
                    v___x_4242_ =
                        l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__1;
                    leanh::lean_inc(v_c_4241_);
                    v___x_4243_ = l_Lean_Syntax_isOfKind(v_c_4241_, v___x_4242_);
                    if v___x_4243_ == 0 {
                        leanh::lean_dec(v_c_4241_);
                        leanh::lean_dec(v_qrhs_4029_);
                        leanh::lean_dec(v_pat_4028_);
                        leanh::lean_dec(v_attrKind_4027_);
                        v___x_4244_ = leanh::lean_box(0);
                        v___x_4245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4245_, 0, v___x_4244_);
                        leanh::lean_ctor_set(v___x_4245_, 1, v_a_4031_);
                        return v___x_4245_;
                    } else {
                        v___x_4246_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4247_ = l_Lean_Syntax_getArg(v_qrhs_4029_, v___x_4246_);
                        leanh::lean_dec(v_qrhs_4029_);
                        v_args_4248_ = l_Lean_Syntax_getArgs(v___x_4247_);
                        leanh::lean_dec(v___x_4247_);
                        v_fst_4037_ = v_c_4241_;
                        v_snd_4038_ = v_args_4248_;
                        v___y_4039_ = v_a_4030_;
                        v___y_4040_ = v_a_4031_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4034_ = leanh::lean_box(0);
                v___x_4035_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4035_, 0, v___x_4034_);
                leanh::lean_ctor_set(v___x_4035_, 1, v___y_4033_);
                return v___x_4035_;
            }
            2 => {
                v___x_4041_ = l_Lean_TSyntax_getId(v_fst_4037_);
                leanh::lean_dec(v_fst_4037_);
                v___x_4042_ = l_Lean_Macro_resolveGlobalName(v___x_4041_, v___y_4039_, v___y_4040_);
                if leanh::lean_obj_tag(v___x_4042_) == 0 {
                    v_a_4043_ = leanh::lean_ctor_get(v___x_4042_, 0);
                    leanh::lean_inc(v_a_4043_);
                    if leanh::lean_obj_tag(v_a_4043_) == 1 {
                        v_head_4044_ = leanh::lean_ctor_get(v_a_4043_, 0);
                        leanh::lean_inc(v_head_4044_);
                        v_snd_4045_ = leanh::lean_ctor_get(v_head_4044_, 1);
                        leanh::lean_inc(v_snd_4045_);
                        if leanh::lean_obj_tag(v_snd_4045_) == 0 {
                            v_tail_4046_ = leanh::lean_ctor_get(v_a_4043_, 1);
                            v_isSharedCheck_4220_ =
                                (!leanh::lean_is_exclusive(v_a_4043_)) as u8;
                            if v_isSharedCheck_4220_ == 0 {
                                v_unused_4221_ = leanh::lean_ctor_get(v_a_4043_, 0);
                                leanh::lean_dec(v_unused_4221_);
                                v___x_4048_ = v_a_4043_;
                                v_isShared_4049_ = v_isSharedCheck_4220_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_tail_4046_);
                                leanh::lean_dec(v_a_4043_);
                                v___x_4048_ = leanh::lean_box(0);
                                v_isShared_4049_ = v_isSharedCheck_4220_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_snd_4045_);
                            leanh::lean_dec_ref_known(v_a_4043_, 2);
                            leanh::lean_dec(v_head_4044_);
                            leanh::lean_dec_ref(v_snd_4038_);
                            leanh::lean_dec(v_pat_4028_);
                            leanh::lean_dec(v_attrKind_4027_);
                            v_a_4222_ = leanh::lean_ctor_get(v___x_4042_, 1);
                            leanh::lean_inc(v_a_4222_);
                            leanh::lean_dec_ref_known(v___x_4042_, 2);
                            v___y_4033_ = v_a_4222_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_4043_);
                        leanh::lean_dec_ref(v_snd_4038_);
                        leanh::lean_dec(v_pat_4028_);
                        leanh::lean_dec(v_attrKind_4027_);
                        v_a_4223_ = leanh::lean_ctor_get(v___x_4042_, 1);
                        leanh::lean_inc(v_a_4223_);
                        leanh::lean_dec_ref_known(v___x_4042_, 2);
                        v___y_4033_ = v_a_4223_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_snd_4038_);
                    leanh::lean_dec(v_pat_4028_);
                    leanh::lean_dec(v_attrKind_4027_);
                    v_a_4224_ = leanh::lean_ctor_get(v___x_4042_, 0);
                    v_a_4225_ = leanh::lean_ctor_get(v___x_4042_, 1);
                    v_isSharedCheck_4232_ = (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4232_ == 0 {
                        v___x_4227_ = v___x_4042_;
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4225_);
                        leanh::lean_inc(v_a_4224_);
                        leanh::lean_dec(v___x_4042_);
                        v___x_4227_ = leanh::lean_box(0);
                        v_isShared_4228_ = v_isSharedCheck_4232_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_tail_4046_) == 0 {
                    v_a_4050_ = leanh::lean_ctor_get(v___x_4042_, 1);
                    leanh::lean_inc(v_a_4050_);
                    leanh::lean_dec_ref_known(v___x_4042_, 2);
                    v_fst_4051_ = leanh::lean_ctor_get(v_head_4044_, 0);
                    v_isSharedCheck_4217_ = (!leanh::lean_is_exclusive(v_head_4044_)) as u8;
                    if v_isSharedCheck_4217_ == 0 {
                        v_unused_4218_ = leanh::lean_ctor_get(v_head_4044_, 1);
                        leanh::lean_dec(v_unused_4218_);
                        v___x_4053_ = v_head_4044_;
                        v_isShared_4054_ = v_isSharedCheck_4217_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_4051_);
                        leanh::lean_dec(v_head_4044_);
                        v___x_4053_ = leanh::lean_box(0);
                        v_isShared_4054_ = v_isSharedCheck_4217_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4048_);
                    leanh::lean_dec(v_tail_4046_);
                    leanh::lean_dec(v_head_4044_);
                    leanh::lean_dec_ref(v_snd_4038_);
                    leanh::lean_dec(v_pat_4028_);
                    leanh::lean_dec(v_attrKind_4027_);
                    v_a_4219_ = leanh::lean_ctor_get(v___x_4042_, 1);
                    leanh::lean_inc(v_a_4219_);
                    leanh::lean_dec_ref_known(v___x_4042_, 2);
                    v___y_4033_ = v_a_4219_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v_sz_4055_ = lean_array_size(v_snd_4038_);
                v___x_4056_ = 0usize;
                v___x_4057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_removeParentheses_spec__0(v_sz_4055_, v___x_4056_, v_snd_4038_, v___y_4039_, v_a_4050_);
                if leanh::lean_obj_tag(v___x_4057_) == 0 {
                    v_a_4058_ = leanh::lean_ctor_get(v___x_4057_, 0);
                    v_a_4059_ = leanh::lean_ctor_get(v___x_4057_, 1);
                    v_isSharedCheck_4207_ = (!leanh::lean_is_exclusive(v___x_4057_)) as u8;
                    if v_isSharedCheck_4207_ == 0 {
                        v___x_4061_ = v___x_4057_;
                        v_isShared_4062_ = v_isSharedCheck_4207_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4059_);
                        leanh::lean_inc(v_a_4058_);
                        leanh::lean_dec(v___x_4057_);
                        v___x_4061_ = leanh::lean_box(0);
                        v_isShared_4062_ = v_isSharedCheck_4207_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4053_);
                    leanh::lean_dec(v_fst_4051_);
                    leanh::lean_del_object(v___x_4048_);
                    leanh::lean_dec(v_pat_4028_);
                    leanh::lean_dec(v_attrKind_4027_);
                    v_a_4208_ = leanh::lean_ctor_get(v___x_4057_, 0);
                    v_a_4209_ = leanh::lean_ctor_get(v___x_4057_, 1);
                    v_isSharedCheck_4216_ = (!leanh::lean_is_exclusive(v___x_4057_)) as u8;
                    if v_isSharedCheck_4216_ == 0 {
                        v___x_4211_ = v___x_4057_;
                        v_isShared_4212_ = v_isSharedCheck_4216_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4209_);
                        leanh::lean_inc(v_a_4208_);
                        leanh::lean_dec(v___x_4057_);
                        v___x_4211_ = leanh::lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4216_;
                        state = 10;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4063_ = l_Lean_Elab_Command_hasDuplicateAntiquot(v_a_4058_);
                if v___x_4063_ == 0 {
                    v_quotContext_4064_ = leanh::lean_ctor_get(v___y_4039_, 1);
                    v_currMacroScope_4065_ = leanh::lean_ctor_get(v___y_4039_, 2);
                    v_ref_4066_ = leanh::lean_ctor_get(v___y_4039_, 5);
                    v___x_4067_ = l_Lean_SourceInfo_fromRef(v_ref_4066_, v___x_4063_);
                    v___x_4068_ =
                        l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__0;
                    v___x_4069_ = l_Lean_Elab_Command_mkUnexpander___closed__1;
                    v___x_4070_ = l_Lean_Elab_Command_mkUnexpander___closed__2;
                    leanh::lean_inc(v___x_4067_);
                    if v_isShared_4054_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_4053_, 2);
                        leanh::lean_ctor_set(v___x_4053_, 1, v___x_4070_);
                        leanh::lean_ctor_set(v___x_4053_, 0, v___x_4067_);
                        v___x_4072_ = v___x_4053_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4202_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 0, v___x_4067_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4202_, 1, v___x_4070_);
                        v___x_4072_ = v_reuseFailAlloc_4202_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4058_);
                    leanh::lean_del_object(v___x_4053_);
                    leanh::lean_dec(v_fst_4051_);
                    leanh::lean_del_object(v___x_4048_);
                    leanh::lean_dec(v_pat_4028_);
                    leanh::lean_dec(v_attrKind_4027_);
                    v___x_4203_ = leanh::lean_box(0);
                    if v_isShared_4062_ == 0 {
                        leanh::lean_ctor_set(v___x_4061_, 0, v___x_4203_);
                        v___x_4205_ = v___x_4061_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4206_, 1, v_a_4059_);
                        v___x_4205_ = v_reuseFailAlloc_4206_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4073_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13;
                v___x_4074_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
                leanh::lean_inc_n(v___x_4067_, 18);
                v___x_4075_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4075_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4075_, 1, v___x_4073_);
                leanh::lean_ctor_set(v___x_4075_, 2, v___x_4074_);
                v___x_4076_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__4_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__4,
                );
                v___x_4077_ = l_Lean_Elab_Command_mkUnexpander___closed__5;
                leanh::lean_inc_n(v_currMacroScope_4065_, 4);
                leanh::lean_inc_n(v_quotContext_4064_, 4);
                v___x_4078_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4077_, v_currMacroScope_4065_);
                v___x_4079_ = leanh::lean_box(0);
                v___x_4080_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4080_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4080_, 1, v___x_4076_);
                leanh::lean_ctor_set(v___x_4080_, 2, v___x_4078_);
                leanh::lean_ctor_set(v___x_4080_, 3, v___x_4079_);
                v___x_4081_ = l_Lean_Elab_Command_mkUnexpander___closed__7;
                v___x_4082_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
                v___x_4083_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4083_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4083_, 1, v___x_4082_);
                v___x_4084_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4084_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4084_, 1, v___x_4068_);
                leanh::lean_inc_ref(v___x_4083_);
                v___x_4085_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4081_, v___x_4083_, v___x_4084_);
                leanh::lean_inc_ref(v___x_4080_);
                leanh::lean_inc_ref(v___x_4075_);
                v___x_4086_ = l_Lean_Syntax_node4(
                    v___x_4067_,
                    v___x_4069_,
                    v___x_4072_,
                    v___x_4075_,
                    v___x_4080_,
                    v___x_4085_,
                );
                v___x_4087_ = l_Lean_Syntax_mkApp(v___x_4086_, v_a_4058_);
                leanh::lean_inc(v_attrKind_4027_);
                v___x_4088_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_4027_);
                v___x_4089_ = l_Lean_Elab_Command_mkUnexpander___closed__9;
                v___x_4090_ = l_Lean_Elab_Command_mkUnexpander___closed__10;
                v___x_4091_ = l_Lean_Elab_Command_mkUnexpander___closed__12;
                v___x_4092_ = l_Lean_Elab_Command_mkUnexpander___closed__13;
                v___x_4093_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4093_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4093_, 1, v___x_4092_);
                v___x_4094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__4;
                v___x_4095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__9;
                v___x_4096_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__15_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__15,
                );
                v___x_4097_ = l_Lean_Elab_Command_mkUnexpander___closed__16;
                v___x_4098_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4097_, v_currMacroScope_4065_);
                v___x_4099_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4099_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4099_, 1, v___x_4096_);
                leanh::lean_ctor_set(v___x_4099_, 2, v___x_4098_);
                leanh::lean_ctor_set(v___x_4099_, 3, v___x_4079_);
                v___x_4100_ = lean_mk_syntax_ident(v_fst_4051_);
                leanh::lean_inc(v___x_4100_);
                v___x_4101_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4100_);
                v___x_4102_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4095_, v___x_4099_, v___x_4101_);
                v___x_4103_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4094_, v_attrKind_4027_, v___x_4102_);
                v___x_4104_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4103_);
                v___x_4105_ = l_Lean_Elab_Command_mkUnexpander___closed__17;
                v___x_4106_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4106_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4106_, 1, v___x_4105_);
                v___x_4107_ = l_Lean_Syntax_node3(
                    v___x_4067_,
                    v___x_4091_,
                    v___x_4093_,
                    v___x_4104_,
                    v___x_4106_,
                );
                v___x_4108_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4107_);
                v___x_4109_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4109_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4109_, 1, v___x_4089_);
                v___x_4110_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__19),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__19_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__19,
                );
                v___x_4111_ = l_Lean_Elab_Command_mkUnexpander___closed__20;
                v___x_4112_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4111_, v_currMacroScope_4065_);
                v___x_4113_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4113_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4113_, 1, v___x_4110_);
                leanh::lean_ctor_set(v___x_4113_, 2, v___x_4112_);
                leanh::lean_ctor_set(v___x_4113_, 3, v___x_4079_);
                v___x_4114_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4073_, v___x_4113_, v___x_4100_);
                v___x_4115_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__22),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__22_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__22,
                );
                v___x_4116_ = l_Lean_Elab_Command_mkUnexpander___closed__25;
                v___x_4117_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4116_, v_currMacroScope_4065_);
                v___x_4118_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4118_, 0, v___x_4116_);
                leanh::lean_ctor_set(v___x_4118_, 1, v_snd_4045_);
                if v_isShared_4049_ == 0 {
                    leanh::lean_ctor_set(v___x_4048_, 1, v___x_4079_);
                    leanh::lean_ctor_set(v___x_4048_, 0, v___x_4118_);
                    v___x_4120_ = v___x_4048_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4201_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 0, v___x_4118_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4201_, 1, v___x_4079_);
                    v___x_4120_ = v_reuseFailAlloc_4201_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                leanh::lean_inc_n(v___x_4067_, 31);
                v___x_4121_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4121_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4121_, 1, v___x_4115_);
                leanh::lean_ctor_set(v___x_4121_, 2, v___x_4117_);
                leanh::lean_ctor_set(v___x_4121_, 3, v___x_4120_);
                v___x_4122_ = l_Lean_Elab_Command_mkUnexpander___closed__26;
                v___x_4123_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4123_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4123_, 1, v___x_4122_);
                v___x_4124_ = l_Lean_Elab_Command_mkUnexpander___closed__27;
                v___x_4125_ = l_Lean_Elab_Command_mkUnexpander___closed__28;
                v___x_4126_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4126_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4126_, 1, v___x_4124_);
                v___x_4127_ = l_Lean_Elab_Command_mkUnexpander___closed__30;
                v___x_4128_ = l_Lean_Elab_Command_mkUnexpander___closed__32;
                v___x_4129_ = l_Lean_Elab_Command_mkUnexpander___closed__33;
                v___x_4130_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4130_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4130_, 1, v___x_4129_);
                v___x_4131_ = l_Lean_Elab_Command_mkUnexpander___closed__35;
                v___x_4132_ = l_Lean_Elab_Command_mkUnexpander___closed__36;
                v___x_4133_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4133_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4133_, 1, v___x_4132_);
                v___x_4134_ = l_Lean_Elab_Command_mkUnexpander___closed__37;
                v___x_4135_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4135_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4135_, 1, v___x_4134_);
                leanh::lean_inc_ref_n(v___x_4135_, 2);
                leanh::lean_inc_ref(v___x_4133_);
                v___x_4136_ = l_Lean_Syntax_node3(
                    v___x_4067_,
                    v___x_4131_,
                    v___x_4133_,
                    v___x_4087_,
                    v___x_4135_,
                );
                v___x_4137_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4136_);
                v___x_4138_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4137_);
                v___x_4139_ = l_Lean_Elab_Command_mkUnexpander___closed__38;
                v___x_4140_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4140_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = l_Lean_Elab_Command_addInheritDocDefault___closed__1;
                v___x_4142_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__40),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__40_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__40,
                );
                v___x_4143_ = l_Lean_Elab_Command_mkUnexpander___closed__41;
                leanh::lean_inc_n(v_currMacroScope_4065_, 3);
                leanh::lean_inc_n(v_quotContext_4064_, 3);
                v___x_4144_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4143_, v_currMacroScope_4065_);
                v___x_4145_ = l_Lean_Elab_Command_mkUnexpander___closed__42;
                v___x_4146_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4146_, 0, v___x_4145_);
                leanh::lean_ctor_set(v___x_4146_, 1, v_snd_4045_);
                v___x_4147_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4147_, 0, v___x_4146_);
                leanh::lean_ctor_set(v___x_4147_, 1, v___x_4079_);
                v___x_4148_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4148_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4148_, 1, v___x_4142_);
                leanh::lean_ctor_set(v___x_4148_, 2, v___x_4144_);
                leanh::lean_ctor_set(v___x_4148_, 3, v___x_4147_);
                v___x_4149_ = l_Lean_Syntax_node3(
                    v___x_4067_,
                    v___x_4131_,
                    v___x_4133_,
                    v_pat_4028_,
                    v___x_4135_,
                );
                v___x_4150_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4073_, v___x_4080_, v___x_4149_);
                v___x_4151_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4141_, v___x_4148_, v___x_4150_);
                leanh::lean_inc_ref(v___x_4140_);
                leanh::lean_inc_ref(v___x_4130_);
                v___x_4152_ = l_Lean_Syntax_node4(
                    v___x_4067_,
                    v___x_4128_,
                    v___x_4130_,
                    v___x_4138_,
                    v___x_4140_,
                    v___x_4151_,
                );
                v___x_4153_ = l_Lean_Elab_Command_mkUnexpander___closed__44;
                v___x_4154_ = l_Lean_Elab_Command_mkUnexpander___closed__45;
                v___x_4155_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4155_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4155_, 1, v___x_4154_);
                v___x_4156_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4153_, v___x_4155_);
                v___x_4157_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4156_);
                v___x_4158_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4157_);
                v___x_4159_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__47),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__47_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__47,
                );
                v___x_4160_ = l_Lean_Elab_Command_mkUnexpander___closed__48;
                v___x_4161_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4160_, v_currMacroScope_4065_);
                v___x_4162_ = l_Lean_Elab_Command_mkUnexpander___closed__50;
                v___x_4163_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4163_, 0, v___x_4162_);
                leanh::lean_ctor_set(v___x_4163_, 1, v_snd_4045_);
                v___x_4164_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4164_, 0, v___x_4163_);
                leanh::lean_ctor_set(v___x_4164_, 1, v___x_4079_);
                v___x_4165_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4165_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4165_, 1, v___x_4159_);
                leanh::lean_ctor_set(v___x_4165_, 2, v___x_4161_);
                leanh::lean_ctor_set(v___x_4165_, 3, v___x_4164_);
                v___x_4166_ = l_Lean_Elab_Command_mkUnexpander___closed__52;
                v___x_4167_ = l_Lean_Elab_Command_removeParentheses___closed__3;
                v___x_4168_ = l_Lean_Elab_Command_mkUnexpander___closed__53;
                v___x_4169_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4169_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4169_, 1, v___x_4168_);
                v___x_4170_ = l_Lean_Elab_Command_removeParentheses___closed__5;
                v___x_4171_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__55),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_mkUnexpander___closed__55_once),
                    _init_l_Lean_Elab_Command_mkUnexpander___closed__55,
                );
                v___x_4172_ = leanh::lean_box(0);
                v___x_4173_ =
                    l_Lean_addMacroScope(v_quotContext_4064_, v___x_4172_, v_currMacroScope_4065_);
                v___x_4174_ = l_Lean_Elab_Command_mkUnexpander___closed__67;
                v___x_4175_ = leanh::lean_alloc_ctor(3, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_4175_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4175_, 1, v___x_4171_);
                leanh::lean_ctor_set(v___x_4175_, 2, v___x_4173_);
                leanh::lean_ctor_set(v___x_4175_, 3, v___x_4174_);
                v___x_4176_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4170_, v___x_4175_);
                v___x_4177_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4167_, v___x_4169_, v___x_4176_);
                leanh::lean_inc_ref(v___x_4075_);
                v___x_4178_ = l_Lean_Syntax_node3(
                    v___x_4067_,
                    v___x_4166_,
                    v___x_4177_,
                    v___x_4075_,
                    v___x_4135_,
                );
                v___x_4179_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4073_, v___x_4178_);
                v___x_4180_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4141_, v___x_4165_, v___x_4179_);
                v___x_4181_ = l_Lean_Syntax_node4(
                    v___x_4067_,
                    v___x_4128_,
                    v___x_4130_,
                    v___x_4158_,
                    v___x_4140_,
                    v___x_4180_,
                );
                v___x_4182_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4073_, v___x_4152_, v___x_4181_);
                v___x_4183_ = l_Lean_Syntax_node1(v___x_4067_, v___x_4127_, v___x_4182_);
                v___x_4184_ =
                    l_Lean_Syntax_node2(v___x_4067_, v___x_4125_, v___x_4126_, v___x_4183_);
                v___x_4185_ = leanh::lean_unsigned_to_nat(9);
                v___x_4186_ = lean_mk_empty_array_with_capacity(v___x_4185_);
                v___x_4187_ = lean_array_push(v___x_4186_, v___x_4075_);
                v___x_4188_ = lean_array_push(v___x_4187_, v___x_4108_);
                v___x_4189_ = lean_array_push(v___x_4188_, v___x_4088_);
                v___x_4190_ = lean_array_push(v___x_4189_, v___x_4109_);
                v___x_4191_ = lean_array_push(v___x_4190_, v___x_4114_);
                v___x_4192_ = lean_array_push(v___x_4191_, v___x_4083_);
                v___x_4193_ = lean_array_push(v___x_4192_, v___x_4121_);
                v___x_4194_ = lean_array_push(v___x_4193_, v___x_4123_);
                v___x_4195_ = lean_array_push(v___x_4194_, v___x_4184_);
                v___x_4196_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4196_, 0, v___x_4067_);
                leanh::lean_ctor_set(v___x_4196_, 1, v___x_4090_);
                leanh::lean_ctor_set(v___x_4196_, 2, v___x_4195_);
                v___x_4197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4197_, 0, v___x_4196_);
                if v_isShared_4062_ == 0 {
                    leanh::lean_ctor_set(v___x_4061_, 0, v___x_4197_);
                    v___x_4199_ = v___x_4061_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4200_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4200_, 1, v_a_4059_);
                    v___x_4199_ = v_reuseFailAlloc_4200_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4199_;
            }
            9 => {
                return v___x_4205_;
            }
            10 => {
                if v_isShared_4212_ == 0 {
                    v___x_4214_ = v___x_4211_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4215_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4215_, 1, v_a_4209_);
                    v___x_4214_ = v_reuseFailAlloc_4215_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4214_;
            }
            12 => {
                if v_isShared_4228_ == 0 {
                    v___x_4230_ = v___x_4227_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4231_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4231_, 1, v_a_4225_);
                    v___x_4230_ = v_reuseFailAlloc_4231_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4230_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_mkUnexpander___boxed(
    mut v_attrKind_4249_: *mut leanh::LeanObject,
    mut v_pat_4250_: *mut leanh::LeanObject,
    mut v_qrhs_4251_: *mut leanh::LeanObject,
    mut v_a_4252_: *mut leanh::LeanObject,
    mut v_a_4253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4254_ = l_Lean_Elab_Command_mkUnexpander(
        v_attrKind_4249_,
        v_pat_4250_,
        v_qrhs_4251_,
        v_a_4252_,
        v_a_4253_,
    );
    leanh::lean_dec_ref(v_a_4252_);
    return v_res_4254_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = leanh::lean_box(0);
    v___x_4256_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4257_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4257_, 0, v___x_4256_);
    leanh::lean_ctor_set(v___x_4257_, 1, v___x_4255_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4259_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___closed__0);
    v___x_4260_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4260_, 0, v___x_4259_);
    return v___x_4260_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg___boxed(
    mut v___y_4261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4262_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(
        );
    return v_res_4262_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(
    mut v_00_u03b1_4263_: *mut leanh::LeanObject,
    mut v___y_4264_: *mut leanh::LeanObject,
    mut v___y_4265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4267_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg(
        );
    return v___x_4267_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___boxed(
    mut v_00_u03b1_4268_: *mut leanh::LeanObject,
    mut v___y_4269_: *mut leanh::LeanObject,
    mut v___y_4270_: *mut leanh::LeanObject,
    mut v___y_4271_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4272_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0(
            v_00_u03b1_4268_,
            v___y_4269_,
            v___y_4270_,
        );
    leanh::lean_dec(v___y_4270_);
    leanh::lean_dec_ref(v___y_4269_);
    return v_res_4272_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(
    mut v___y_4273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4275_ = lean_st_ref_get(v___y_4273_);
    v_env_4276_ = leanh::lean_ctor_get(v___x_4275_, 0);
    leanh::lean_inc_ref(v_env_4276_);
    leanh::lean_dec(v___x_4275_);
    v___x_4277_ = l_Lean_Environment_header(v_env_4276_);
    leanh::lean_dec_ref(v_env_4276_);
    v_mainModule_4278_ = leanh::lean_ctor_get(v___x_4277_, 0);
    leanh::lean_inc(v_mainModule_4278_);
    leanh::lean_dec_ref(v___x_4277_);
    v___x_4279_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4279_, 0, v_mainModule_4278_);
    return v___x_4279_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg___boxed(
    mut v___y_4280_: *mut leanh::LeanObject,
    mut v___y_4281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4282_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_4280_);
    leanh::lean_dec(v___y_4280_);
    return v_res_4282_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(
    mut v___y_4283_: *mut leanh::LeanObject,
    mut v___y_4284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ =
        l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_4284_);
    return v___x_4286_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___boxed(
    mut v___y_4287_: *mut leanh::LeanObject,
    mut v___y_4288_: *mut leanh::LeanObject,
    mut v___y_4289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4290_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7(
        v___y_4287_,
        v___y_4288_,
    );
    leanh::lean_dec(v___y_4288_);
    leanh::lean_dec_ref(v___y_4287_);
    return v_res_4290_;
}
pub unsafe fn l_Lean_Elab_Command_elabNotation___lam__0(
    mut v___x_4291_: *mut leanh::LeanObject,
    mut v_sc_4292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_header_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelNames_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varDecls_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varUIds_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_includedVars_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_omittedVars_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNoncomputable_4301_: u8 = 0;
    let mut v_isPublic_4302_: u8 = 0;
    let mut v_isMeta_4303_: u8 = 0;
    let mut v_attrs_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4307_: u8 = 0;
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v_unused_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_4293_ = leanh::lean_ctor_get(v_sc_4292_, 0);
                v_currNamespace_4294_ = leanh::lean_ctor_get(v_sc_4292_, 2);
                v_openDecls_4295_ = leanh::lean_ctor_get(v_sc_4292_, 3);
                v_levelNames_4296_ = leanh::lean_ctor_get(v_sc_4292_, 4);
                v_varDecls_4297_ = leanh::lean_ctor_get(v_sc_4292_, 5);
                v_varUIds_4298_ = leanh::lean_ctor_get(v_sc_4292_, 6);
                v_includedVars_4299_ = leanh::lean_ctor_get(v_sc_4292_, 7);
                v_omittedVars_4300_ = leanh::lean_ctor_get(v_sc_4292_, 8);
                v_isNoncomputable_4301_ = leanh::lean_ctor_get_uint8(
                    v_sc_4292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                );
                v_isPublic_4302_ = leanh::lean_ctor_get_uint8(
                    v_sc_4292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1) as u32,
                );
                v_isMeta_4303_ = leanh::lean_ctor_get_uint8(
                    v_sc_4292_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2) as u32,
                );
                v_attrs_4304_ = leanh::lean_ctor_get(v_sc_4292_, 9);
                v_isSharedCheck_4311_ = (!leanh::lean_is_exclusive(v_sc_4292_)) as u8;
                if v_isSharedCheck_4311_ == 0 {
                    v_unused_4312_ = leanh::lean_ctor_get(v_sc_4292_, 1);
                    leanh::lean_dec(v_unused_4312_);
                    v___x_4306_ = v_sc_4292_;
                    v_isShared_4307_ = v_isSharedCheck_4311_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_attrs_4304_);
                    leanh::lean_inc(v_omittedVars_4300_);
                    leanh::lean_inc(v_includedVars_4299_);
                    leanh::lean_inc(v_varUIds_4298_);
                    leanh::lean_inc(v_varDecls_4297_);
                    leanh::lean_inc(v_levelNames_4296_);
                    leanh::lean_inc(v_openDecls_4295_);
                    leanh::lean_inc(v_currNamespace_4294_);
                    leanh::lean_inc(v_header_4293_);
                    leanh::lean_dec(v_sc_4292_);
                    v___x_4306_ = leanh::lean_box(0);
                    v_isShared_4307_ = v_isSharedCheck_4311_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_4307_ == 0 {
                    leanh::lean_ctor_set(v___x_4306_, 1, v___x_4291_);
                    v___x_4309_ = v___x_4306_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4310_ = leanh::lean_alloc_ctor(0, 10, (3) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_header_4293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 1, v___x_4291_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 2, v_currNamespace_4294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 3, v_openDecls_4295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 4, v_levelNames_4296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 5, v_varDecls_4297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 6, v_varUIds_4298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 7, v_includedVars_4299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 8, v_omittedVars_4300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 9, v_attrs_4304_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4310_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_isNoncomputable_4301_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4310_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 1) as u32,
                        v_isPublic_4302_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_4310_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10 + 2) as u32,
                        v_isMeta_4303_,
                    );
                    v___x_4309_ = v_reuseFailAlloc_4310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(
    mut v_sz_4313_: usize,
    mut v_i_4314_: usize,
    mut v_bs_4315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4316_: u8 = 0;
    let mut v_v_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: usize = 0;
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4316_ = lean_usize_dec_lt(v_i_4314_, v_sz_4313_);
                if v___x_4316_ == 0 {
                    return v_bs_4315_;
                } else {
                    v_v_4317_ = lean_array_uget(v_bs_4315_, v_i_4314_);
                    v___x_4318_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4319_ = lean_array_uset(v_bs_4315_, v_i_4314_, v___x_4318_);
                    v___x_4320_ = 1usize;
                    v___x_4321_ = lean_usize_add(v_i_4314_, v___x_4320_);
                    v___x_4322_ = lean_array_uset(v_bs_x27_4319_, v_i_4314_, v_v_4317_);
                    v_i_4314_ = v___x_4321_;
                    v_bs_4315_ = v___x_4322_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3___boxed(
    mut v_sz_4324_: *mut leanh::LeanObject,
    mut v_i_4325_: *mut leanh::LeanObject,
    mut v_bs_4326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4327_: usize = 0;
    let mut v_i_boxed_4328_: usize = 0;
    let mut v_res_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4327_ = leanh::lean_unbox_usize(v_sz_4324_);
    leanh::lean_dec(v_sz_4324_);
    v_i_boxed_4328_ = leanh::lean_unbox_usize(v_i_4325_);
    leanh::lean_dec(v_i_4325_);
    v_res_4329_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_boxed_4327_, v_i_boxed_4328_, v_bs_4326_);
    return v_res_4329_;
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(
    mut v_o_4333_: *mut leanh::LeanObject,
    mut v_k_4334_: *mut leanh::LeanObject,
    mut v_v_4335_: u8,
) -> *mut leanh::LeanObject {
    let mut v_map_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4337_: u8 = 0;
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4340_: u8 = 0;
    let mut v___x_4341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: u8 = 0;
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4351_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_4336_ = leanh::lean_ctor_get(v_o_4333_, 0);
                v_hasTrace_4337_ = leanh::lean_ctor_get_uint8(
                    v_o_4333_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_4351_ = (!leanh::lean_is_exclusive(v_o_4333_)) as u8;
                if v_isSharedCheck_4351_ == 0 {
                    v___x_4339_ = v_o_4333_;
                    v_isShared_4340_ = v_isSharedCheck_4351_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_map_4336_);
                    leanh::lean_dec(v_o_4333_);
                    v___x_4339_ = leanh::lean_box(0);
                    v_isShared_4340_ = v_isSharedCheck_4351_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4341_ = leanh::lean_alloc_ctor(1, 0, (1) as u32);
                leanh::lean_ctor_set_uint8(v___x_4341_, 0 as u32, v_v_4335_);
                leanh::lean_inc(v_k_4334_);
                v___x_4342_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_4334_, v___x_4341_, v_map_4336_);
                if v_hasTrace_4337_ == 0 {
                    v___x_4343_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1;
                    v___x_4344_ = l_Lean_Name_isPrefixOf(v___x_4343_, v_k_4334_);
                    leanh::lean_dec(v_k_4334_);
                    if v_isShared_4340_ == 0 {
                        leanh::lean_ctor_set(v___x_4339_, 0, v___x_4342_);
                        v___x_4346_ = v___x_4339_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4347_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4347_, 0, v___x_4342_);
                        v___x_4346_ = v_reuseFailAlloc_4347_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_k_4334_);
                    if v_isShared_4340_ == 0 {
                        leanh::lean_ctor_set(v___x_4339_, 0, v___x_4342_);
                        v___x_4349_ = v___x_4339_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4350_ = leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4350_, 0, v___x_4342_);
                        leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4350_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_4337_,
                        );
                        v___x_4349_ = v_reuseFailAlloc_4350_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_4346_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4344_,
                );
                return v___x_4346_;
            }
            3 => {
                return v___x_4349_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___boxed(
    mut v_o_4352_: *mut leanh::LeanObject,
    mut v_k_4353_: *mut leanh::LeanObject,
    mut v_v_4354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_boxed_4355_: u8 = 0;
    let mut v_res_4356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v_boxed_4355_ = (leanh::lean_unbox(v_v_4354_) as u8);
    v_res_4356_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_o_4352_, v_k_4353_, v_v_boxed_4355_);
    return v_res_4356_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(
    mut v_opts_4357_: *mut leanh::LeanObject,
    mut v_opt_4358_: *mut leanh::LeanObject,
    mut v_val_4359_: u8,
) -> *mut leanh::LeanObject {
    let mut v_name_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4360_ = leanh::lean_ctor_get(v_opt_4358_, 0);
    leanh::lean_inc(v_name_4360_);
    leanh::lean_dec_ref(v_opt_4358_);
    v___x_4361_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13(v_opts_4357_, v_name_4360_, v_val_4359_);
    return v___x_4361_;
}
pub unsafe fn l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6___boxed(
    mut v_opts_4362_: *mut leanh::LeanObject,
    mut v_opt_4363_: *mut leanh::LeanObject,
    mut v_val_4364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_boxed_4365_: u8 = 0;
    let mut v_res_4366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_val_boxed_4365_ = (leanh::lean_unbox(v_val_4364_) as u8);
    v_res_4366_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(
        v_opts_4362_,
        v_opt_4363_,
        v_val_boxed_4365_,
    );
    return v_res_4366_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(
    mut v_sz_4367_: usize,
    mut v_i_4368_: usize,
    mut v_bs_4369_: *mut leanh::LeanObject,
    mut v___y_4370_: *mut leanh::LeanObject,
    mut v___y_4371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4372_: u8 = 0;
    let mut v___x_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: usize = 0;
    let mut v___x_4381_: usize = 0;
    let mut v___x_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4388_: u8 = 0;
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4392_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4372_ = lean_usize_dec_lt(v_i_4368_, v_sz_4367_);
                if v___x_4372_ == 0 {
                    v___x_4373_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4373_, 0, v_bs_4369_);
                    leanh::lean_ctor_set(v___x_4373_, 1, v___y_4371_);
                    return v___x_4373_;
                } else {
                    v_v_4374_ = lean_array_uget_borrowed(v_bs_4369_, v_i_4368_);
                    leanh::lean_inc(v_v_4374_);
                    v___x_4375_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem(
                        v_v_4374_,
                        v___y_4370_,
                        v___y_4371_,
                    );
                    if leanh::lean_obj_tag(v___x_4375_) == 0 {
                        v_a_4376_ = leanh::lean_ctor_get(v___x_4375_, 0);
                        leanh::lean_inc(v_a_4376_);
                        v_a_4377_ = leanh::lean_ctor_get(v___x_4375_, 1);
                        leanh::lean_inc(v_a_4377_);
                        leanh::lean_dec_ref_known(v___x_4375_, 2);
                        v___x_4378_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4379_ = lean_array_uset(v_bs_4369_, v_i_4368_, v___x_4378_);
                        v___x_4380_ = 1usize;
                        v___x_4381_ = lean_usize_add(v_i_4368_, v___x_4380_);
                        v___x_4382_ = lean_array_uset(v_bs_x27_4379_, v_i_4368_, v_a_4376_);
                        v_i_4368_ = v___x_4381_;
                        v_bs_4369_ = v___x_4382_;
                        v___y_4371_ = v_a_4377_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4369_);
                        v_a_4384_ = leanh::lean_ctor_get(v___x_4375_, 0);
                        v_a_4385_ = leanh::lean_ctor_get(v___x_4375_, 1);
                        v_isSharedCheck_4392_ =
                            (!leanh::lean_is_exclusive(v___x_4375_)) as u8;
                        if v_isSharedCheck_4392_ == 0 {
                            v___x_4387_ = v___x_4375_;
                            v_isShared_4388_ = v_isSharedCheck_4392_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4385_);
                            leanh::lean_inc(v_a_4384_);
                            leanh::lean_dec(v___x_4375_);
                            v___x_4387_ = leanh::lean_box(0);
                            v_isShared_4388_ = v_isSharedCheck_4392_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4388_ == 0 {
                    v___x_4390_ = v___x_4387_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4391_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4384_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_a_4385_);
                    v___x_4390_ = v_reuseFailAlloc_4391_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4390_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed(
    mut v_sz_4393_: *mut leanh::LeanObject,
    mut v_i_4394_: *mut leanh::LeanObject,
    mut v_bs_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4398_: usize = 0;
    let mut v_i_boxed_4399_: usize = 0;
    let mut v_res_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4398_ = leanh::lean_unbox_usize(v_sz_4393_);
    leanh::lean_dec(v_sz_4393_);
    v_i_boxed_4399_ = leanh::lean_unbox_usize(v_i_4394_);
    leanh::lean_dec(v_i_4394_);
    v_res_4400_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2(v_sz_boxed_4398_, v_i_boxed_4399_, v_bs_4395_, v___y_4396_, v___y_4397_);
    leanh::lean_dec_ref(v___y_4396_);
    return v_res_4400_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(
    mut v_sz_4401_: usize,
    mut v_i_4402_: usize,
    mut v_bs_4403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4404_: u8 = 0;
    let mut v___x_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: usize = 0;
    let mut v___x_4410_: usize = 0;
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4404_ = lean_usize_dec_lt(v_i_4402_, v_sz_4401_);
                if v___x_4404_ == 0 {
                    return v_bs_4403_;
                } else {
                    v___x_4405_ = leanh::lean_unsigned_to_nat(0);
                    v_v_4406_ = lean_array_uget(v_bs_4403_, v_i_4402_);
                    v_bs_x27_4407_ = lean_array_uset(v_bs_4403_, v_i_4402_, v___x_4405_);
                    v___x_4408_ = l_Lean_Syntax_getArg(v_v_4406_, v___x_4405_);
                    leanh::lean_dec(v_v_4406_);
                    v___x_4409_ = 1usize;
                    v___x_4410_ = lean_usize_add(v_i_4402_, v___x_4409_);
                    v___x_4411_ = lean_array_uset(v_bs_x27_4407_, v_i_4402_, v___x_4408_);
                    v_i_4402_ = v___x_4410_;
                    v_bs_4403_ = v___x_4411_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5___boxed(
    mut v_sz_4413_: *mut leanh::LeanObject,
    mut v_i_4414_: *mut leanh::LeanObject,
    mut v_bs_4415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4416_: usize = 0;
    let mut v_i_boxed_4417_: usize = 0;
    let mut v_res_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4416_ = leanh::lean_unbox_usize(v_sz_4413_);
    leanh::lean_dec(v_sz_4413_);
    v_i_boxed_4417_ = leanh::lean_unbox_usize(v_i_4414_);
    leanh::lean_dec(v_i_4414_);
    v_res_4418_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_boxed_4416_, v_i_boxed_4417_, v_bs_4415_);
    return v_res_4418_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(
    mut v_sz_4419_: usize,
    mut v_i_4420_: usize,
    mut v_bs_4421_: *mut leanh::LeanObject,
    mut v___y_4422_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4423_: u8 = 0;
    let mut v___x_4424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: usize = 0;
    let mut v___x_4432_: usize = 0;
    let mut v___x_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4439_: u8 = 0;
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4423_ = lean_usize_dec_lt(v_i_4420_, v_sz_4419_);
                if v___x_4423_ == 0 {
                    v___x_4424_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4424_, 0, v_bs_4421_);
                    leanh::lean_ctor_set(v___x_4424_, 1, v___y_4422_);
                    return v___x_4424_;
                } else {
                    v_v_4425_ = lean_array_uget_borrowed(v_bs_4421_, v_i_4420_);
                    leanh::lean_inc(v_v_4425_);
                    v___x_4426_ = l_Lean_Elab_Command_expandNotationItemIntoPattern___redArg(
                        v_v_4425_,
                        v___y_4422_,
                    );
                    if leanh::lean_obj_tag(v___x_4426_) == 0 {
                        v_a_4427_ = leanh::lean_ctor_get(v___x_4426_, 0);
                        leanh::lean_inc(v_a_4427_);
                        v_a_4428_ = leanh::lean_ctor_get(v___x_4426_, 1);
                        leanh::lean_inc(v_a_4428_);
                        leanh::lean_dec_ref_known(v___x_4426_, 2);
                        v___x_4429_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4430_ = lean_array_uset(v_bs_4421_, v_i_4420_, v___x_4429_);
                        v___x_4431_ = 1usize;
                        v___x_4432_ = lean_usize_add(v_i_4420_, v___x_4431_);
                        v___x_4433_ = lean_array_uset(v_bs_x27_4430_, v_i_4420_, v_a_4427_);
                        v_i_4420_ = v___x_4432_;
                        v_bs_4421_ = v___x_4433_;
                        v___y_4422_ = v_a_4428_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_4421_);
                        v_a_4435_ = leanh::lean_ctor_get(v___x_4426_, 0);
                        v_a_4436_ = leanh::lean_ctor_get(v___x_4426_, 1);
                        v_isSharedCheck_4443_ =
                            (!leanh::lean_is_exclusive(v___x_4426_)) as u8;
                        if v_isSharedCheck_4443_ == 0 {
                            v___x_4438_ = v___x_4426_;
                            v_isShared_4439_ = v_isSharedCheck_4443_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4436_);
                            leanh::lean_inc(v_a_4435_);
                            leanh::lean_dec(v___x_4426_);
                            v___x_4438_ = leanh::lean_box(0);
                            v_isShared_4439_ = v_isSharedCheck_4443_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4439_ == 0 {
                    v___x_4441_ = v___x_4438_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4435_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 1, v_a_4436_);
                    v___x_4441_ = v_reuseFailAlloc_4442_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg___boxed(
    mut v_sz_4444_: *mut leanh::LeanObject,
    mut v_i_4445_: *mut leanh::LeanObject,
    mut v_bs_4446_: *mut leanh::LeanObject,
    mut v___y_4447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4448_: usize = 0;
    let mut v_i_boxed_4449_: usize = 0;
    let mut v_res_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4448_ = leanh::lean_unbox_usize(v_sz_4444_);
    leanh::lean_dec(v_sz_4444_);
    v_i_boxed_4449_ = leanh::lean_unbox_usize(v_i_4445_);
    leanh::lean_dec(v_i_4445_);
    v_res_4450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_boxed_4448_, v_i_boxed_4449_, v_bs_4446_, v___y_4447_);
    return v_res_4450_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(
    mut v_sz_4451_: usize,
    mut v_i_4452_: usize,
    mut v_bs_4453_: *mut leanh::LeanObject,
    mut v___y_4454_: *mut leanh::LeanObject,
    mut v___y_4455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___redArg(v_sz_4451_, v_i_4452_, v_bs_4453_, v___y_4455_);
    return v___x_4456_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed(
    mut v_sz_4457_: *mut leanh::LeanObject,
    mut v_i_4458_: *mut leanh::LeanObject,
    mut v_bs_4459_: *mut leanh::LeanObject,
    mut v___y_4460_: *mut leanh::LeanObject,
    mut v___y_4461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4462_: usize = 0;
    let mut v_i_boxed_4463_: usize = 0;
    let mut v_res_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4462_ = leanh::lean_unbox_usize(v_sz_4457_);
    leanh::lean_dec(v_sz_4457_);
    v_i_boxed_4463_ = leanh::lean_unbox_usize(v_i_4458_);
    leanh::lean_dec(v_i_4458_);
    v_res_4464_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4(v_sz_boxed_4462_, v_i_boxed_4463_, v_bs_4459_, v___y_4460_, v___y_4461_);
    leanh::lean_dec_ref(v___y_4460_);
    return v_res_4464_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(
    mut v_env_4465_: *mut leanh::LeanObject,
    mut v_currNamespace_4466_: *mut leanh::LeanObject,
    mut v_openDecls_4467_: *mut leanh::LeanObject,
    mut v_n_4468_: *mut leanh::LeanObject,
    mut v___y_4469_: *mut leanh::LeanObject,
    mut v___y_4470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4471_ = l_Lean_ResolveName_resolveNamespace(
        v_env_4465_,
        v_currNamespace_4466_,
        v_openDecls_4467_,
        v_n_4468_,
    );
    v___x_4472_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4472_, 0, v___x_4471_);
    leanh::lean_ctor_set(v___x_4472_, 1, v___y_4470_);
    return v___x_4472_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed(
    mut v_env_4473_: *mut leanh::LeanObject,
    mut v_currNamespace_4474_: *mut leanh::LeanObject,
    mut v_openDecls_4475_: *mut leanh::LeanObject,
    mut v_n_4476_: *mut leanh::LeanObject,
    mut v___y_4477_: *mut leanh::LeanObject,
    mut v___y_4478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4479_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3(
            v_env_4473_,
            v_currNamespace_4474_,
            v_openDecls_4475_,
            v_n_4476_,
            v___y_4477_,
            v___y_4478_,
        );
    leanh::lean_dec_ref(v___y_4477_);
    return v_res_4479_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4480_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4480_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_4482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4482_, 0, v___x_4481_);
    return v___x_4482_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4483_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_4484_ = leanh::lean_unsigned_to_nat(0);
    v___x_4485_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_4485_, 0, v___x_4484_);
    leanh::lean_ctor_set(v___x_4485_, 1, v___x_4484_);
    leanh::lean_ctor_set(v___x_4485_, 2, v___x_4484_);
    leanh::lean_ctor_set(v___x_4485_, 3, v___x_4484_);
    leanh::lean_ctor_set(v___x_4485_, 4, v___x_4483_);
    leanh::lean_ctor_set(v___x_4485_, 5, v___x_4483_);
    leanh::lean_ctor_set(v___x_4485_, 6, v___x_4483_);
    leanh::lean_ctor_set(v___x_4485_, 7, v___x_4483_);
    leanh::lean_ctor_set(v___x_4485_, 8, v___x_4483_);
    leanh::lean_ctor_set(v___x_4485_, 9, v___x_4483_);
    return v___x_4485_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4486_ = leanh::lean_unsigned_to_nat(32);
    v___x_4487_ = lean_mk_empty_array_with_capacity(v___x_4486_);
    v___x_4488_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4488_, 0, v___x_4487_);
    return v___x_4488_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4489_: usize = 0;
    let mut v___x_4490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4489_ = 5usize;
    v___x_4490_ = leanh::lean_unsigned_to_nat(0);
    v___x_4491_ = leanh::lean_unsigned_to_nat(32);
    v___x_4492_ = lean_mk_empty_array_with_capacity(v___x_4491_);
    v___x_4493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__3);
    v___x_4494_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_4494_, 0, v___x_4493_);
    leanh::lean_ctor_set(v___x_4494_, 1, v___x_4492_);
    leanh::lean_ctor_set(v___x_4494_, 2, v___x_4490_);
    leanh::lean_ctor_set(v___x_4494_, 3, v___x_4490_);
    leanh::lean_ctor_set_usize(v___x_4494_, 4, v___x_4489_);
    return v___x_4494_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4495_ = leanh::lean_box(1);
    v___x_4496_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__4);
    v___x_4497_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__1);
    v___x_4498_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_4498_, 0, v___x_4497_);
    leanh::lean_ctor_set(v___x_4498_, 1, v___x_4496_);
    leanh::lean_ctor_set(v___x_4498_, 2, v___x_4495_);
    return v___x_4498_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(
    mut v_msgData_4499_: *mut leanh::LeanObject,
    mut v___y_4500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4502_ = lean_st_ref_get(v___y_4500_);
    v_env_4503_ = leanh::lean_ctor_get(v___x_4502_, 0);
    leanh::lean_inc_ref(v_env_4503_);
    leanh::lean_dec(v___x_4502_);
    v___x_4504_ = lean_st_ref_get(v___y_4500_);
    v_scopes_4505_ = leanh::lean_ctor_get(v___x_4504_, 2);
    leanh::lean_inc(v_scopes_4505_);
    leanh::lean_dec(v___x_4504_);
    v___x_4506_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_4507_ = l_List_head_x21___redArg(v___x_4506_, v_scopes_4505_);
    leanh::lean_dec(v_scopes_4505_);
    v_opts_4508_ = leanh::lean_ctor_get(v___x_4507_, 1);
    leanh::lean_inc_ref(v_opts_4508_);
    leanh::lean_dec(v___x_4507_);
    v___x_4509_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__2);
    v___x_4510_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___closed__5);
    v___x_4511_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4511_, 0, v_env_4503_);
    leanh::lean_ctor_set(v___x_4511_, 1, v___x_4509_);
    leanh::lean_ctor_set(v___x_4511_, 2, v___x_4510_);
    leanh::lean_ctor_set(v___x_4511_, 3, v_opts_4508_);
    v___x_4512_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
    leanh::lean_ctor_set(v___x_4512_, 1, v_msgData_4499_);
    v___x_4513_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4513_, 0, v___x_4512_);
    return v___x_4513_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_msgData_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4517_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_4514_, v___y_4515_);
    leanh::lean_dec(v___y_4515_);
    return v_res_4517_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0()
-> f64 {
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: f64 = 0.0;
    v___x_4518_ = leanh::lean_unsigned_to_nat(0);
    v___x_4519_ = lean_float_of_nat(v___x_4518_);
    return v___x_4519_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(
    mut v_cls_4522_: *mut leanh::LeanObject,
    mut v_msg_4523_: *mut leanh::LeanObject,
    mut v___y_4524_: *mut leanh::LeanObject,
    mut v___y_4525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4533_: u8 = 0;
    let mut v___x_4534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4548_: u8 = 0;
    let mut v_tid_4549_: u64 = 0;
    let mut v_traces_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4553_: u8 = 0;
    let mut v___x_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: f64 = 0.0;
    let mut v___x_4556_: u8 = 0;
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4574_: u8 = 0;
    let mut v_isSharedCheck_4575_: u8 = 0;
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut v_a_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4580_: u8 = 0;
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4527_ = l_Lean_Elab_Command_getRef___redArg(v___y_4524_);
                if leanh::lean_obj_tag(v___x_4527_) == 0 {
                    v_a_4528_ = leanh::lean_ctor_get(v___x_4527_, 0);
                    leanh::lean_inc(v_a_4528_);
                    leanh::lean_dec_ref_known(v___x_4527_, 1);
                    v___x_4529_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_4523_, v___y_4525_);
                    v_a_4530_ = leanh::lean_ctor_get(v___x_4529_, 0);
                    v_isSharedCheck_4576_ = (!leanh::lean_is_exclusive(v___x_4529_)) as u8;
                    if v_isSharedCheck_4576_ == 0 {
                        v___x_4532_ = v___x_4529_;
                        v_isShared_4533_ = v_isSharedCheck_4576_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4530_);
                        leanh::lean_dec(v___x_4529_);
                        v___x_4532_ = leanh::lean_box(0);
                        v_isShared_4533_ = v_isSharedCheck_4576_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_4523_);
                    leanh::lean_dec(v_cls_4522_);
                    v_a_4577_ = leanh::lean_ctor_get(v___x_4527_, 0);
                    v_isSharedCheck_4584_ = (!leanh::lean_is_exclusive(v___x_4527_)) as u8;
                    if v_isSharedCheck_4584_ == 0 {
                        v___x_4579_ = v___x_4527_;
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4577_);
                        leanh::lean_dec(v___x_4527_);
                        v___x_4579_ = leanh::lean_box(0);
                        v_isShared_4580_ = v_isSharedCheck_4584_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4534_ = lean_st_ref_take(v___y_4525_);
                v_traceState_4535_ = leanh::lean_ctor_get(v___x_4534_, 9);
                v_env_4536_ = leanh::lean_ctor_get(v___x_4534_, 0);
                v_messages_4537_ = leanh::lean_ctor_get(v___x_4534_, 1);
                v_scopes_4538_ = leanh::lean_ctor_get(v___x_4534_, 2);
                v_usedQuotCtxts_4539_ = leanh::lean_ctor_get(v___x_4534_, 3);
                v_nextMacroScope_4540_ = leanh::lean_ctor_get(v___x_4534_, 4);
                v_maxRecDepth_4541_ = leanh::lean_ctor_get(v___x_4534_, 5);
                v_ngen_4542_ = leanh::lean_ctor_get(v___x_4534_, 6);
                v_auxDeclNGen_4543_ = leanh::lean_ctor_get(v___x_4534_, 7);
                v_infoState_4544_ = leanh::lean_ctor_get(v___x_4534_, 8);
                v_snapshotTasks_4545_ = leanh::lean_ctor_get(v___x_4534_, 10);
                v_isSharedCheck_4575_ = (!leanh::lean_is_exclusive(v___x_4534_)) as u8;
                if v_isSharedCheck_4575_ == 0 {
                    v___x_4547_ = v___x_4534_;
                    v_isShared_4548_ = v_isSharedCheck_4575_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_4545_);
                    leanh::lean_inc(v_traceState_4535_);
                    leanh::lean_inc(v_infoState_4544_);
                    leanh::lean_inc(v_auxDeclNGen_4543_);
                    leanh::lean_inc(v_ngen_4542_);
                    leanh::lean_inc(v_maxRecDepth_4541_);
                    leanh::lean_inc(v_nextMacroScope_4540_);
                    leanh::lean_inc(v_usedQuotCtxts_4539_);
                    leanh::lean_inc(v_scopes_4538_);
                    leanh::lean_inc(v_messages_4537_);
                    leanh::lean_inc(v_env_4536_);
                    leanh::lean_dec(v___x_4534_);
                    v___x_4547_ = leanh::lean_box(0);
                    v_isShared_4548_ = v_isSharedCheck_4575_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4549_ = leanh::lean_ctor_get_uint64(
                    v_traceState_4535_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4550_ = leanh::lean_ctor_get(v_traceState_4535_, 0);
                v_isSharedCheck_4574_ =
                    (!leanh::lean_is_exclusive(v_traceState_4535_)) as u8;
                if v_isSharedCheck_4574_ == 0 {
                    v___x_4552_ = v_traceState_4535_;
                    v_isShared_4553_ = v_isSharedCheck_4574_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_4550_);
                    leanh::lean_dec(v_traceState_4535_);
                    v___x_4552_ = leanh::lean_box(0);
                    v_isShared_4553_ = v_isSharedCheck_4574_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4554_ = leanh::lean_box(0);
                v___x_4555_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__0);
                v___x_4556_ = 0;
                v___x_4557_ = l_Lean_Elab_Command_mkUnexpander___closed__54;
                v___x_4558_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_4558_, 0, v_cls_4522_);
                leanh::lean_ctor_set(v___x_4558_, 1, v___x_4554_);
                leanh::lean_ctor_set(v___x_4558_, 2, v___x_4557_);
                leanh::lean_ctor_set_float(
                    v___x_4558_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_4555_,
                );
                leanh::lean_ctor_set_float(
                    v___x_4558_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4555_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_4558_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4556_,
                );
                v___x_4559_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___closed__1;
                v___x_4560_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_4560_, 0, v___x_4558_);
                leanh::lean_ctor_set(v___x_4560_, 1, v_a_4530_);
                leanh::lean_ctor_set(v___x_4560_, 2, v___x_4559_);
                v___x_4561_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4561_, 0, v_a_4528_);
                leanh::lean_ctor_set(v___x_4561_, 1, v___x_4560_);
                v___x_4562_ = l_Lean_PersistentArray_push___redArg(v_traces_4550_, v___x_4561_);
                if v_isShared_4553_ == 0 {
                    leanh::lean_ctor_set(v___x_4552_, 0, v___x_4562_);
                    v___x_4564_ = v___x_4552_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4573_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4573_, 0, v___x_4562_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4573_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_4549_,
                    );
                    v___x_4564_ = v_reuseFailAlloc_4573_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4548_ == 0 {
                    leanh::lean_ctor_set(v___x_4547_, 9, v___x_4564_);
                    v___x_4566_ = v___x_4547_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4572_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_env_4536_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_messages_4537_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 2, v_scopes_4538_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 3, v_usedQuotCtxts_4539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 4, v_nextMacroScope_4540_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 5, v_maxRecDepth_4541_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 6, v_ngen_4542_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 7, v_auxDeclNGen_4543_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 8, v_infoState_4544_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 9, v___x_4564_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4572_, 10, v_snapshotTasks_4545_);
                    v___x_4566_ = v_reuseFailAlloc_4572_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4567_ = lean_st_ref_set(v___y_4525_, v___x_4566_);
                v___x_4568_ = leanh::lean_box(0);
                if v_isShared_4533_ == 0 {
                    leanh::lean_ctor_set(v___x_4532_, 0, v___x_4568_);
                    v___x_4570_ = v___x_4532_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4571_, 0, v___x_4568_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4570_;
            }
            7 => {
                if v_isShared_4580_ == 0 {
                    v___x_4582_ = v___x_4579_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v_a_4577_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1___boxed(
    mut v_cls_4585_: *mut leanh::LeanObject,
    mut v_msg_4586_: *mut leanh::LeanObject,
    mut v___y_4587_: *mut leanh::LeanObject,
    mut v___y_4588_: *mut leanh::LeanObject,
    mut v___y_4589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4590_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_4585_, v_msg_4586_, v___y_4587_, v___y_4588_);
    leanh::lean_dec(v___y_4588_);
    leanh::lean_dec_ref(v___y_4587_);
    return v_res_4590_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(
    mut v_as_4591_: *mut leanh::LeanObject,
    mut v___y_4592_: *mut leanh::LeanObject,
    mut v___y_4593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4608_: u8 = 0;
    let mut v___x_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: u8 = 0;
    let mut v___x_4614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_4591_) == 0 {
                    v___x_4595_ = leanh::lean_box(0);
                    v___x_4596_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4596_, 0, v___x_4595_);
                    return v___x_4596_;
                } else {
                    v_head_4597_ = leanh::lean_ctor_get(v_as_4591_, 0);
                    leanh::lean_inc(v_head_4597_);
                    v_tail_4598_ = leanh::lean_ctor_get(v_as_4591_, 1);
                    leanh::lean_inc(v_tail_4598_);
                    leanh::lean_dec_ref_known(v_as_4591_, 2);
                    v_fst_4599_ = leanh::lean_ctor_get(v_head_4597_, 0);
                    leanh::lean_inc(v_fst_4599_);
                    v_snd_4600_ = leanh::lean_ctor_get(v_head_4597_, 1);
                    leanh::lean_inc(v_snd_4600_);
                    leanh::lean_dec(v_head_4597_);
                    v___x_4601_ = l_Lean_inheritedTraceOptions;
                    v___x_4602_ = lean_st_ref_get(v___x_4601_);
                    v___x_4603_ = lean_st_ref_get(v___y_4593_);
                    v_scopes_4604_ = leanh::lean_ctor_get(v___x_4603_, 2);
                    leanh::lean_inc(v_scopes_4604_);
                    leanh::lean_dec(v___x_4603_);
                    v___x_4605_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_4606_ = l_List_head_x21___redArg(v___x_4605_, v_scopes_4604_);
                    leanh::lean_dec(v_scopes_4604_);
                    v_opts_4607_ = leanh::lean_ctor_get(v___x_4606_, 1);
                    leanh::lean_inc_ref(v_opts_4607_);
                    leanh::lean_dec(v___x_4606_);
                    v_hasTrace_4608_ = leanh::lean_ctor_get_uint8(
                        v_opts_4607_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4608_ == 0 {
                        leanh::lean_dec_ref(v_opts_4607_);
                        leanh::lean_dec(v___x_4602_);
                        leanh::lean_dec(v_snd_4600_);
                        leanh::lean_dec(v_fst_4599_);
                        v_as_4591_ = v_tail_4598_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4610_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1;
                        leanh::lean_inc(v_fst_4599_);
                        v___x_4611_ = l_Lean_Name_append(v___x_4610_, v_fst_4599_);
                        v___x_4612_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_4602_,
                            v_opts_4607_,
                            v___x_4611_,
                        );
                        leanh::lean_dec(v___x_4611_);
                        leanh::lean_dec_ref(v_opts_4607_);
                        leanh::lean_dec(v___x_4602_);
                        if v___x_4612_ == 0 {
                            leanh::lean_dec(v_snd_4600_);
                            leanh::lean_dec(v_fst_4599_);
                            v_as_4591_ = v_tail_4598_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4614_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_4614_, 0, v_snd_4600_);
                            v___x_4615_ = l_Lean_MessageData_ofFormat(v___x_4614_);
                            v___x_4616_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_fst_4599_, v___x_4615_, v___y_4592_, v___y_4593_);
                            if leanh::lean_obj_tag(v___x_4616_) == 0 {
                                leanh::lean_dec_ref_known(v___x_4616_, 1);
                                v_as_4591_ = v_tail_4598_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v_tail_4598_);
                                return v___x_4616_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5___boxed(
    mut v_as_4618_: *mut leanh::LeanObject,
    mut v___y_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4622_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v_as_4618_, v___y_4619_, v___y_4620_);
    leanh::lean_dec(v___y_4620_);
    leanh::lean_dec_ref(v___y_4619_);
    return v_res_4622_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(
    mut v_currNamespace_4623_: *mut leanh::LeanObject,
    mut v___y_4624_: *mut leanh::LeanObject,
    mut v___y_4625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4626_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4626_, 0, v_currNamespace_4623_);
    leanh::lean_ctor_set(v___x_4626_, 1, v___y_4625_);
    return v___x_4626_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed(
    mut v_currNamespace_4627_: *mut leanh::LeanObject,
    mut v___y_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2(
            v_currNamespace_4627_,
            v___y_4628_,
            v___y_4629_,
        );
    leanh::lean_dec_ref(v___y_4628_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(
    mut v_env_4631_: *mut leanh::LeanObject,
    mut v_opts_4632_: *mut leanh::LeanObject,
    mut v_currNamespace_4633_: *mut leanh::LeanObject,
    mut v_openDecls_4634_: *mut leanh::LeanObject,
    mut v_n_4635_: *mut leanh::LeanObject,
    mut v___y_4636_: *mut leanh::LeanObject,
    mut v___y_4637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4638_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_4631_,
        v_opts_4632_,
        v_currNamespace_4633_,
        v_openDecls_4634_,
        v_n_4635_,
    );
    v___x_4639_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4639_, 0, v___x_4638_);
    leanh::lean_ctor_set(v___x_4639_, 1, v___y_4637_);
    return v___x_4639_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed(
    mut v_env_4640_: *mut leanh::LeanObject,
    mut v_opts_4641_: *mut leanh::LeanObject,
    mut v_currNamespace_4642_: *mut leanh::LeanObject,
    mut v_openDecls_4643_: *mut leanh::LeanObject,
    mut v_n_4644_: *mut leanh::LeanObject,
    mut v___y_4645_: *mut leanh::LeanObject,
    mut v___y_4646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4(
            v_env_4640_,
            v_opts_4641_,
            v_currNamespace_4642_,
            v_openDecls_4643_,
            v_n_4644_,
            v___y_4645_,
            v___y_4646_,
        );
    leanh::lean_dec_ref(v___y_4645_);
    leanh::lean_dec_ref(v_opts_4641_);
    return v_res_4647_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4648_ = leanh::lean_box(1);
    v___x_4649_ = l_Lean_MessageData_ofFormat(v___x_4648_);
    return v___x_4649_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4653_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__2;
    v___x_4654_ = l_Lean_MessageData_ofFormat(v___x_4653_);
    return v___x_4654_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(
    mut v_x_4655_: *mut leanh::LeanObject,
    mut v_x_4656_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4661_: u8 = 0;
    let mut v_before_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4665_: u8 = 0;
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4678_: u8 = 0;
    let mut v_unused_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4656_) == 0 {
                    return v_x_4655_;
                } else {
                    v_head_4657_ = leanh::lean_ctor_get(v_x_4656_, 0);
                    v_tail_4658_ = leanh::lean_ctor_get(v_x_4656_, 1);
                    v_isSharedCheck_4680_ = (!leanh::lean_is_exclusive(v_x_4656_)) as u8;
                    if v_isSharedCheck_4680_ == 0 {
                        v___x_4660_ = v_x_4656_;
                        v_isShared_4661_ = v_isSharedCheck_4680_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_4658_);
                        leanh::lean_inc(v_head_4657_);
                        leanh::lean_dec(v_x_4656_);
                        v___x_4660_ = leanh::lean_box(0);
                        v_isShared_4661_ = v_isSharedCheck_4680_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_4662_ = leanh::lean_ctor_get(v_head_4657_, 0);
                v_isSharedCheck_4678_ = (!leanh::lean_is_exclusive(v_head_4657_)) as u8;
                if v_isSharedCheck_4678_ == 0 {
                    v_unused_4679_ = leanh::lean_ctor_get(v_head_4657_, 1);
                    leanh::lean_dec(v_unused_4679_);
                    v___x_4664_ = v_head_4657_;
                    v_isShared_4665_ = v_isSharedCheck_4678_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_before_4662_);
                    leanh::lean_dec(v_head_4657_);
                    v___x_4664_ = leanh::lean_box(0);
                    v_isShared_4665_ = v_isSharedCheck_4678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4666_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
                if v_isShared_4665_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4664_, 7);
                    leanh::lean_ctor_set(v___x_4664_, 1, v___x_4666_);
                    leanh::lean_ctor_set(v___x_4664_, 0, v_x_4655_);
                    v___x_4668_ = v___x_4664_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4677_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 0, v_x_4655_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4677_, 1, v___x_4666_);
                    v___x_4668_ = v_reuseFailAlloc_4677_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4669_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__3);
                if v_isShared_4661_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4660_, 7);
                    leanh::lean_ctor_set(v___x_4660_, 1, v___x_4669_);
                    leanh::lean_ctor_set(v___x_4660_, 0, v___x_4668_);
                    v___x_4671_ = v___x_4660_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4676_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4668_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4676_, 1, v___x_4669_);
                    v___x_4671_ = v_reuseFailAlloc_4676_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4672_ = l_Lean_MessageData_ofSyntax(v_before_4662_);
                v___x_4673_ = l_Lean_indentD(v___x_4672_);
                v___x_4674_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4674_, 0, v___x_4671_);
                leanh::lean_ctor_set(v___x_4674_, 1, v___x_4673_);
                v_x_4655_ = v___x_4674_;
                v_x_4656_ = v_tail_4658_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(
    mut v_opts_4681_: *mut leanh::LeanObject,
    mut v_opt_4682_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_4683_ = leanh::lean_ctor_get(v_opt_4682_, 0);
    v_defValue_4684_ = leanh::lean_ctor_get(v_opt_4682_, 1);
    v_map_4685_ = leanh::lean_ctor_get(v_opts_4681_, 0);
    v___x_4686_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4685_,
            v_name_4683_,
        );
    if leanh::lean_obj_tag(v___x_4686_) == 0 {
        let mut v___x_4687_: u8 = 0;
        v___x_4687_ = (leanh::lean_unbox(v_defValue_4684_) as u8);
        return v___x_4687_;
    } else {
        let mut v_val_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_4688_ = leanh::lean_ctor_get(v___x_4686_, 0);
        leanh::lean_inc(v_val_4688_);
        leanh::lean_dec_ref_known(v___x_4686_, 1);
        if leanh::lean_obj_tag(v_val_4688_) == 1 {
            let mut v_v_4689_: u8 = 0;
            v_v_4689_ = leanh::lean_ctor_get_uint8(v_val_4688_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_4688_, 0);
            return v_v_4689_;
        } else {
            let mut v___x_4690_: u8 = 0;
            leanh::lean_dec(v_val_4688_);
            v___x_4690_ = (leanh::lean_unbox(v_defValue_4684_) as u8);
            return v___x_4690_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25___boxed(
    mut v_opts_4691_: *mut leanh::LeanObject,
    mut v_opt_4692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4693_: u8 = 0;
    let mut v_r_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4693_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_4691_, v_opt_4692_);
    leanh::lean_dec_ref(v_opt_4692_);
    leanh::lean_dec_ref(v_opts_4691_);
    v_r_4694_ = leanh::lean_box((v_res_4693_) as usize);
    return v_r_4694_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4698_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__1;
    v___x_4699_ = l_Lean_MessageData_ofFormat(v___x_4698_);
    return v___x_4699_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(
    mut v_msgData_4700_: *mut leanh::LeanObject,
    mut v_macroStack_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_4705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: u8 = 0;
    let mut v___x_4711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4717_: u8 = 0;
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4729_: u8 = 0;
    let mut v_unused_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4704_ = lean_st_ref_get(v___y_4702_);
                v_scopes_4705_ = leanh::lean_ctor_get(v___x_4704_, 2);
                leanh::lean_inc(v_scopes_4705_);
                leanh::lean_dec(v___x_4704_);
                v___x_4706_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_4707_ = l_List_head_x21___redArg(v___x_4706_, v_scopes_4705_);
                leanh::lean_dec(v_scopes_4705_);
                v_opts_4708_ = leanh::lean_ctor_get(v___x_4707_, 1);
                leanh::lean_inc_ref(v_opts_4708_);
                leanh::lean_dec(v___x_4707_);
                v___x_4709_ = l_Lean_Elab_pp_macroStack;
                v___x_4710_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__25(v_opts_4708_, v___x_4709_);
                leanh::lean_dec_ref(v_opts_4708_);
                if v___x_4710_ == 0 {
                    leanh::lean_dec(v_macroStack_4701_);
                    v___x_4711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4711_, 0, v_msgData_4700_);
                    return v___x_4711_;
                } else {
                    if leanh::lean_obj_tag(v_macroStack_4701_) == 0 {
                        v___x_4712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4712_, 0, v_msgData_4700_);
                        return v___x_4712_;
                    } else {
                        v_head_4713_ = leanh::lean_ctor_get(v_macroStack_4701_, 0);
                        leanh::lean_inc(v_head_4713_);
                        v_after_4714_ = leanh::lean_ctor_get(v_head_4713_, 1);
                        v_isSharedCheck_4729_ =
                            (!leanh::lean_is_exclusive(v_head_4713_)) as u8;
                        if v_isSharedCheck_4729_ == 0 {
                            v_unused_4730_ = leanh::lean_ctor_get(v_head_4713_, 0);
                            leanh::lean_dec(v_unused_4730_);
                            v___x_4716_ = v_head_4713_;
                            v_isShared_4717_ = v_isSharedCheck_4729_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_after_4714_);
                            leanh::lean_dec(v_head_4713_);
                            v___x_4716_ = leanh::lean_box(0);
                            v_isShared_4717_ = v_isSharedCheck_4729_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4718_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26___closed__0);
                if v_isShared_4717_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4716_, 7);
                    leanh::lean_ctor_set(v___x_4716_, 1, v___x_4718_);
                    leanh::lean_ctor_set(v___x_4716_, 0, v_msgData_4700_);
                    v___x_4720_ = v___x_4716_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4728_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_msgData_4700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4728_, 1, v___x_4718_);
                    v___x_4720_ = v_reuseFailAlloc_4728_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4721_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___closed__2);
                v___x_4722_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4722_, 0, v___x_4720_);
                leanh::lean_ctor_set(v___x_4722_, 1, v___x_4721_);
                v___x_4723_ = l_Lean_MessageData_ofSyntax(v_after_4714_);
                v___x_4724_ = l_Lean_indentD(v___x_4723_);
                v_msgData_4725_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v_msgData_4725_, 0, v___x_4722_);
                leanh::lean_ctor_set(v_msgData_4725_, 1, v___x_4724_);
                v___x_4726_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23_spec__26(v_msgData_4725_, v_macroStack_4701_);
                v___x_4727_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4727_, 0, v___x_4726_);
                return v___x_4727_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg___boxed(
    mut v_msgData_4731_: *mut leanh::LeanObject,
    mut v_macroStack_4732_: *mut leanh::LeanObject,
    mut v___y_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4735_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_4731_, v_macroStack_4732_, v___y_4733_);
    leanh::lean_dec(v___y_4733_);
    return v_res_4735_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(
    mut v_msg_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4750_: u8 = 0;
    let mut v___x_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4755_: u8 = 0;
    let mut v_a_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4759_: u8 = 0;
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4740_ = l_Lean_Elab_Command_getRef___redArg(v___y_4737_);
                if leanh::lean_obj_tag(v___x_4740_) == 0 {
                    v_a_4741_ = leanh::lean_ctor_get(v___x_4740_, 0);
                    leanh::lean_inc(v_a_4741_);
                    leanh::lean_dec_ref_known(v___x_4740_, 1);
                    v_macroStack_4742_ = leanh::lean_ctor_get(v___y_4737_, 4);
                    v___x_4743_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msg_4736_, v___y_4738_);
                    v_a_4744_ = leanh::lean_ctor_get(v___x_4743_, 0);
                    leanh::lean_inc(v_a_4744_);
                    leanh::lean_dec_ref(v___x_4743_);
                    v___x_4745_ = l_Lean_Elab_getBetterRef(v_a_4741_, v_macroStack_4742_);
                    leanh::lean_dec(v_a_4741_);
                    leanh::lean_inc(v_macroStack_4742_);
                    v___x_4746_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_a_4744_, v_macroStack_4742_, v___y_4738_);
                    v_a_4747_ = leanh::lean_ctor_get(v___x_4746_, 0);
                    v_isSharedCheck_4755_ = (!leanh::lean_is_exclusive(v___x_4746_)) as u8;
                    if v_isSharedCheck_4755_ == 0 {
                        v___x_4749_ = v___x_4746_;
                        v_isShared_4750_ = v_isSharedCheck_4755_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4747_);
                        leanh::lean_dec(v___x_4746_);
                        v___x_4749_ = leanh::lean_box(0);
                        v_isShared_4750_ = v_isSharedCheck_4755_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_msg_4736_);
                    v_a_4756_ = leanh::lean_ctor_get(v___x_4740_, 0);
                    v_isSharedCheck_4763_ = (!leanh::lean_is_exclusive(v___x_4740_)) as u8;
                    if v_isSharedCheck_4763_ == 0 {
                        v___x_4758_ = v___x_4740_;
                        v_isShared_4759_ = v_isSharedCheck_4763_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4756_);
                        leanh::lean_dec(v___x_4740_);
                        v___x_4758_ = leanh::lean_box(0);
                        v_isShared_4759_ = v_isSharedCheck_4763_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4751_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4751_, 0, v___x_4745_);
                leanh::lean_ctor_set(v___x_4751_, 1, v_a_4747_);
                if v_isShared_4750_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4749_, 1);
                    leanh::lean_ctor_set(v___x_4749_, 0, v___x_4751_);
                    v___x_4753_ = v___x_4749_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4754_, 0, v___x_4751_);
                    v___x_4753_ = v_reuseFailAlloc_4754_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4753_;
            }
            3 => {
                if v_isShared_4759_ == 0 {
                    v___x_4761_ = v___x_4758_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4762_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
                    v___x_4761_ = v_reuseFailAlloc_4762_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg___boxed(
    mut v_msg_4764_: *mut leanh::LeanObject,
    mut v___y_4765_: *mut leanh::LeanObject,
    mut v___y_4766_: *mut leanh::LeanObject,
    mut v___y_4767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4768_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_4764_, v___y_4765_, v___y_4766_);
    leanh::lean_dec(v___y_4766_);
    leanh::lean_dec_ref(v___y_4765_);
    return v_res_4768_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(
    mut v_ref_4769_: *mut leanh::LeanObject,
    mut v_msg_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_4779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4785_: u8 = 0;
    let mut v_ref_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4792_: u8 = 0;
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4774_ = l_Lean_Elab_Command_getRef___redArg(v___y_4771_);
                if leanh::lean_obj_tag(v___x_4774_) == 0 {
                    v_a_4775_ = leanh::lean_ctor_get(v___x_4774_, 0);
                    leanh::lean_inc(v_a_4775_);
                    leanh::lean_dec_ref_known(v___x_4774_, 1);
                    v_fileName_4776_ = leanh::lean_ctor_get(v___y_4771_, 0);
                    v_fileMap_4777_ = leanh::lean_ctor_get(v___y_4771_, 1);
                    v_currRecDepth_4778_ = leanh::lean_ctor_get(v___y_4771_, 2);
                    v_cmdPos_4779_ = leanh::lean_ctor_get(v___y_4771_, 3);
                    v_macroStack_4780_ = leanh::lean_ctor_get(v___y_4771_, 4);
                    v_quotContext_x3f_4781_ = leanh::lean_ctor_get(v___y_4771_, 5);
                    v_currMacroScope_4782_ = leanh::lean_ctor_get(v___y_4771_, 6);
                    v_snap_x3f_4783_ = leanh::lean_ctor_get(v___y_4771_, 8);
                    v_cancelTk_x3f_4784_ = leanh::lean_ctor_get(v___y_4771_, 9);
                    v_suppressElabErrors_4785_ = leanh::lean_ctor_get_uint8(
                        v___y_4771_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_4786_ = l_Lean_replaceRef(v_ref_4769_, v_a_4775_);
                    leanh::lean_dec(v_a_4775_);
                    leanh::lean_inc(v_cancelTk_x3f_4784_);
                    leanh::lean_inc(v_snap_x3f_4783_);
                    leanh::lean_inc(v_currMacroScope_4782_);
                    leanh::lean_inc(v_quotContext_x3f_4781_);
                    leanh::lean_inc(v_macroStack_4780_);
                    leanh::lean_inc(v_cmdPos_4779_);
                    leanh::lean_inc(v_currRecDepth_4778_);
                    leanh::lean_inc_ref(v_fileMap_4777_);
                    leanh::lean_inc_ref(v_fileName_4776_);
                    v___x_4787_ = leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    leanh::lean_ctor_set(v___x_4787_, 0, v_fileName_4776_);
                    leanh::lean_ctor_set(v___x_4787_, 1, v_fileMap_4777_);
                    leanh::lean_ctor_set(v___x_4787_, 2, v_currRecDepth_4778_);
                    leanh::lean_ctor_set(v___x_4787_, 3, v_cmdPos_4779_);
                    leanh::lean_ctor_set(v___x_4787_, 4, v_macroStack_4780_);
                    leanh::lean_ctor_set(v___x_4787_, 5, v_quotContext_x3f_4781_);
                    leanh::lean_ctor_set(v___x_4787_, 6, v_currMacroScope_4782_);
                    leanh::lean_ctor_set(v___x_4787_, 7, v_ref_4786_);
                    leanh::lean_ctor_set(v___x_4787_, 8, v_snap_x3f_4783_);
                    leanh::lean_ctor_set(v___x_4787_, 9, v_cancelTk_x3f_4784_);
                    leanh::lean_ctor_set_uint8(
                        v___x_4787_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_4785_,
                    );
                    v___x_4788_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_4770_, v___x_4787_, v___y_4772_);
                    leanh::lean_dec_ref_known(v___x_4787_, 10);
                    return v___x_4788_;
                } else {
                    leanh::lean_dec_ref(v_msg_4770_);
                    v_a_4789_ = leanh::lean_ctor_get(v___x_4774_, 0);
                    v_isSharedCheck_4796_ = (!leanh::lean_is_exclusive(v___x_4774_)) as u8;
                    if v_isSharedCheck_4796_ == 0 {
                        v___x_4791_ = v___x_4774_;
                        v_isShared_4792_ = v_isSharedCheck_4796_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4789_);
                        leanh::lean_dec(v___x_4774_);
                        v___x_4791_ = leanh::lean_box(0);
                        v_isShared_4792_ = v_isSharedCheck_4796_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4792_ == 0 {
                    v___x_4794_ = v___x_4791_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4795_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_a_4789_);
                    v___x_4794_ = v_reuseFailAlloc_4795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg___boxed(
    mut v_ref_4797_: *mut leanh::LeanObject,
    mut v_msg_4798_: *mut leanh::LeanObject,
    mut v___y_4799_: *mut leanh::LeanObject,
    mut v___y_4800_: *mut leanh::LeanObject,
    mut v___y_4801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4802_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_4797_, v_msg_4798_, v___y_4799_, v___y_4800_);
    leanh::lean_dec(v___y_4800_);
    leanh::lean_dec_ref(v___y_4799_);
    leanh::lean_dec(v_ref_4797_);
    return v_res_4802_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(
    mut v_env_4803_: *mut leanh::LeanObject,
    mut v_declName_4804_: *mut leanh::LeanObject,
    mut v___y_4805_: *mut leanh::LeanObject,
    mut v___y_4806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4807_: u8 = 0;
    let mut v_env_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: u8 = 0;
    let mut v___x_4811_: u8 = 0;
    v___x_4807_ = 0;
    v_env_4808_ = l_Lean_Environment_setExporting(v_env_4803_, v___x_4807_);
    leanh::lean_inc(v_declName_4804_);
    v___x_4809_ = l_Lean_mkPrivateName(v_env_4808_, v_declName_4804_);
    v___x_4810_ = 1;
    leanh::lean_inc_ref(v_env_4808_);
    v___x_4811_ = l_Lean_Environment_contains(v_env_4808_, v___x_4809_, v___x_4810_);
    if v___x_4811_ == 0 {
        let mut v___x_4812_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4813_: u8 = 0;
        let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4815_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4812_ = l_Lean_privateToUserName(v_declName_4804_);
        v___x_4813_ = l_Lean_Environment_contains(v_env_4808_, v___x_4812_, v___x_4810_);
        v___x_4814_ = leanh::lean_box((v___x_4813_) as usize);
        v___x_4815_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4815_, 0, v___x_4814_);
        leanh::lean_ctor_set(v___x_4815_, 1, v___y_4806_);
        return v___x_4815_;
    } else {
        let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_env_4808_);
        leanh::lean_dec(v_declName_4804_);
        v___x_4816_ = leanh::lean_box((v___x_4811_) as usize);
        v___x_4817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4817_, 0, v___x_4816_);
        leanh::lean_ctor_set(v___x_4817_, 1, v___y_4806_);
        return v___x_4817_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed(
    mut v_env_4818_: *mut leanh::LeanObject,
    mut v_declName_4819_: *mut leanh::LeanObject,
    mut v___y_4820_: *mut leanh::LeanObject,
    mut v___y_4821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4822_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0(
            v_env_4818_,
            v_declName_4819_,
            v___y_4820_,
            v___y_4821_,
        );
    leanh::lean_dec_ref(v___y_4820_);
    return v_res_4822_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(
    mut v_x_4823_: *mut leanh::LeanObject,
    mut v___y_4824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_4823_) == 0 {
        let mut v_a_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4825_ = leanh::lean_ctor_get(v_x_4823_, 0);
        leanh::lean_inc(v_a_4825_);
        v___x_4826_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4826_, 0, v_a_4825_);
        leanh::lean_ctor_set(v___x_4826_, 1, v___y_4824_);
        return v___x_4826_;
    } else {
        let mut v_a_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_4827_ = leanh::lean_ctor_get(v_x_4823_, 0);
        leanh::lean_inc(v_a_4827_);
        v___x_4828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_4828_, 0, v_a_4827_);
        leanh::lean_ctor_set(v___x_4828_, 1, v___y_4824_);
        return v___x_4828_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg___boxed(
    mut v_x_4829_: *mut leanh::LeanObject,
    mut v___y_4830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4831_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_4829_, v___y_4830_);
    leanh::lean_dec_ref(v_x_4829_);
    return v_res_4831_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(
    mut v_env_4832_: *mut leanh::LeanObject,
    mut v_stx_4833_: *mut leanh::LeanObject,
    mut v___y_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4841_: u8 = 0;
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut v_unused_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v_snd_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4857_: u8 = 0;
    let mut v___x_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v_a_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4875_: u8 = 0;
    let mut v_isSharedCheck_4876_: u8 = 0;
    let mut v_a_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4881_: u8 = 0;
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4885_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4836_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_4832_,
                    v_stx_4833_,
                    v___y_4834_,
                    v___y_4835_,
                );
                if leanh::lean_obj_tag(v___x_4836_) == 0 {
                    v_a_4837_ = leanh::lean_ctor_get(v___x_4836_, 0);
                    leanh::lean_inc(v_a_4837_);
                    if leanh::lean_obj_tag(v_a_4837_) == 0 {
                        v_a_4838_ = leanh::lean_ctor_get(v___x_4836_, 1);
                        v_isSharedCheck_4846_ =
                            (!leanh::lean_is_exclusive(v___x_4836_)) as u8;
                        if v_isSharedCheck_4846_ == 0 {
                            v_unused_4847_ = leanh::lean_ctor_get(v___x_4836_, 0);
                            leanh::lean_dec(v_unused_4847_);
                            v___x_4840_ = v___x_4836_;
                            v_isShared_4841_ = v_isSharedCheck_4846_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4838_);
                            leanh::lean_dec(v___x_4836_);
                            v___x_4840_ = leanh::lean_box(0);
                            v_isShared_4841_ = v_isSharedCheck_4846_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_4848_ = leanh::lean_ctor_get(v_a_4837_, 0);
                        v_isSharedCheck_4876_ = (!leanh::lean_is_exclusive(v_a_4837_)) as u8;
                        if v_isSharedCheck_4876_ == 0 {
                            v___x_4850_ = v_a_4837_;
                            v_isShared_4851_ = v_isSharedCheck_4876_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4848_);
                            leanh::lean_dec(v_a_4837_);
                            v___x_4850_ = leanh::lean_box(0);
                            v_isShared_4851_ = v_isSharedCheck_4876_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4877_ = leanh::lean_ctor_get(v___x_4836_, 0);
                    v_a_4878_ = leanh::lean_ctor_get(v___x_4836_, 1);
                    v_isSharedCheck_4885_ = (!leanh::lean_is_exclusive(v___x_4836_)) as u8;
                    if v_isSharedCheck_4885_ == 0 {
                        v___x_4880_ = v___x_4836_;
                        v_isShared_4881_ = v_isSharedCheck_4885_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4878_);
                        leanh::lean_inc(v_a_4877_);
                        leanh::lean_dec(v___x_4836_);
                        v___x_4880_ = leanh::lean_box(0);
                        v_isShared_4881_ = v_isSharedCheck_4885_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4842_ = leanh::lean_box(0);
                if v_isShared_4841_ == 0 {
                    leanh::lean_ctor_set(v___x_4840_, 0, v___x_4842_);
                    v___x_4844_ = v___x_4840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v___x_4842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 1, v_a_4838_);
                    v___x_4844_ = v_reuseFailAlloc_4845_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4844_;
            }
            3 => {
                v_snd_4852_ = leanh::lean_ctor_get(v_val_4848_, 1);
                leanh::lean_inc(v_snd_4852_);
                leanh::lean_dec(v_val_4848_);
                if leanh::lean_obj_tag(v_snd_4852_) == 0 {
                    leanh::lean_del_object(v___x_4850_);
                    v_a_4853_ = leanh::lean_ctor_get(v___x_4836_, 1);
                    leanh::lean_inc(v_a_4853_);
                    leanh::lean_dec_ref_known(v___x_4836_, 2);
                    v_a_4854_ = leanh::lean_ctor_get(v_snd_4852_, 0);
                    v_isSharedCheck_4862_ = (!leanh::lean_is_exclusive(v_snd_4852_)) as u8;
                    if v_isSharedCheck_4862_ == 0 {
                        v___x_4856_ = v_snd_4852_;
                        v_isShared_4857_ = v_isSharedCheck_4862_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4854_);
                        leanh::lean_dec(v_snd_4852_);
                        v___x_4856_ = leanh::lean_box(0);
                        v_isShared_4857_ = v_isSharedCheck_4862_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4863_ = leanh::lean_ctor_get(v___x_4836_, 1);
                    leanh::lean_inc(v_a_4863_);
                    leanh::lean_dec_ref_known(v___x_4836_, 2);
                    v_a_4864_ = leanh::lean_ctor_get(v_snd_4852_, 0);
                    v_isSharedCheck_4875_ = (!leanh::lean_is_exclusive(v_snd_4852_)) as u8;
                    if v_isSharedCheck_4875_ == 0 {
                        v___x_4866_ = v_snd_4852_;
                        v_isShared_4867_ = v_isSharedCheck_4875_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4864_);
                        leanh::lean_dec(v_snd_4852_);
                        v___x_4866_ = leanh::lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4875_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4857_ == 0 {
                    v___x_4859_ = v___x_4856_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4854_);
                    v___x_4859_ = v_reuseFailAlloc_4861_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4860_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_4859_, v_a_4853_);
                leanh::lean_dec_ref(v___x_4859_);
                return v___x_4860_;
            }
            6 => {
                if v_isShared_4851_ == 0 {
                    leanh::lean_ctor_set(v___x_4850_, 0, v_a_4864_);
                    v___x_4869_ = v___x_4850_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4874_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4874_, 0, v_a_4864_);
                    v___x_4869_ = v_reuseFailAlloc_4874_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4867_ == 0 {
                    leanh::lean_ctor_set(v___x_4866_, 0, v___x_4869_);
                    v___x_4871_ = v___x_4866_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 0, v___x_4869_);
                    v___x_4871_ = v_reuseFailAlloc_4873_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4872_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v___x_4871_, v_a_4863_);
                leanh::lean_dec_ref(v___x_4871_);
                return v___x_4872_;
            }
            9 => {
                if v_isShared_4881_ == 0 {
                    v___x_4883_ = v___x_4880_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4884_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4884_, 0, v_a_4877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4884_, 1, v_a_4878_);
                    v___x_4883_ = v_reuseFailAlloc_4884_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed(
    mut v_env_4886_: *mut leanh::LeanObject,
    mut v_stx_4887_: *mut leanh::LeanObject,
    mut v___y_4888_: *mut leanh::LeanObject,
    mut v___y_4889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4890_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1(
            v_env_4886_,
            v_stx_4887_,
            v___y_4888_,
            v___y_4889_,
        );
    leanh::lean_dec_ref(v___y_4888_);
    return v_res_4890_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4896_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4897_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4897_, 0, v___x_4896_);
    return v___x_4897_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4898_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__3);
    v___x_4899_ = l_Lean_MessageData_ofFormat(v___x_4898_);
    return v___x_4899_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_4900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4900_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__4);
    v___x_4901_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__2;
    v___x_4902_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4902_, 0, v___x_4901_);
    leanh::lean_ctor_set(v___x_4902_, 1, v___x_4900_);
    return v___x_4902_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(
    mut v_ref_4903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4905_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___closed__5);
    v___x_4906_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4906_, 0, v_ref_4903_);
    leanh::lean_ctor_set(v___x_4906_, 1, v___x_4905_);
    v___x_4907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4907_, 0, v___x_4906_);
    return v___x_4907_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg___boxed(
    mut v_ref_4908_: *mut leanh::LeanObject,
    mut v___y_4909_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4910_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_4908_);
    return v_res_4910_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(
    mut v_keys_4911_: *mut leanh::LeanObject,
    mut v_i_4912_: *mut leanh::LeanObject,
    mut v_k_4913_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: u8 = 0;
    let mut v_k_x27_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4914_ = lean_array_get_size(v_keys_4911_);
                v___x_4915_ = lean_nat_dec_lt(v_i_4912_, v___x_4914_);
                if v___x_4915_ == 0 {
                    leanh::lean_dec(v_i_4912_);
                    return v___x_4915_;
                } else {
                    v_k_x27_4916_ = lean_array_fget_borrowed(v_keys_4911_, v_i_4912_);
                    v___x_4917_ = l_Lean_instBEqExtraModUse_beq(v_k_4913_, v_k_x27_4916_);
                    if v___x_4917_ == 0 {
                        v___x_4918_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4919_ = lean_nat_add(v_i_4912_, v___x_4918_);
                        leanh::lean_dec(v_i_4912_);
                        v_i_4912_ = v___x_4919_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_4912_);
                        return v___x_4917_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg___boxed(
    mut v_keys_4921_: *mut leanh::LeanObject,
    mut v_i_4922_: *mut leanh::LeanObject,
    mut v_k_4923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4924_: u8 = 0;
    let mut v_r_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_4921_, v_i_4922_, v_k_4923_);
    leanh::lean_dec_ref(v_k_4923_);
    leanh::lean_dec_ref(v_keys_4921_);
    v_r_4925_ = leanh::lean_box((v_res_4924_) as usize);
    return v_r_4925_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0()
-> usize {
    let mut v___x_4926_: usize = 0;
    let mut v___x_4927_: usize = 0;
    let mut v___x_4928_: usize = 0;
    v___x_4926_ = 5usize;
    v___x_4927_ = 1usize;
    v___x_4928_ = lean_usize_shift_left(v___x_4927_, v___x_4926_);
    return v___x_4928_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1()
-> usize {
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: usize = 0;
    let mut v___x_4931_: usize = 0;
    v___x_4929_ = 1usize;
    v___x_4930_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__0);
    v___x_4931_ = lean_usize_sub(v___x_4930_, v___x_4929_);
    return v___x_4931_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(
    mut v_x_4932_: *mut leanh::LeanObject,
    mut v_x_4933_: usize,
    mut v_x_4934_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: usize = 0;
    let mut v___x_4938_: usize = 0;
    let mut v___x_4939_: usize = 0;
    let mut v_j_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v_node_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: usize = 0;
    let mut v___x_4947_: u8 = 0;
    let mut v_ks_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4932_) == 0 {
                    v_es_4935_ = leanh::lean_ctor_get(v_x_4932_, 0);
                    v___x_4936_ = leanh::lean_box(2);
                    v___x_4937_ = 5usize;
                    v___x_4938_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___closed__1);
                    v___x_4939_ = lean_usize_land(v_x_4933_, v___x_4938_);
                    v_j_4940_ = lean_usize_to_nat(v___x_4939_);
                    v___x_4941_ = lean_array_get_borrowed(v___x_4936_, v_es_4935_, v_j_4940_);
                    leanh::lean_dec(v_j_4940_);
                    match leanh::lean_obj_tag(v___x_4941_) {
                        0 => {
                            v_key_4942_ = leanh::lean_ctor_get(v___x_4941_, 0);
                            v___x_4943_ = l_Lean_instBEqExtraModUse_beq(v_x_4934_, v_key_4942_);
                            return v___x_4943_;
                        }
                        1 => {
                            v_node_4944_ = leanh::lean_ctor_get(v___x_4941_, 0);
                            v___x_4945_ = lean_usize_shift_right(v_x_4933_, v___x_4937_);
                            v_x_4932_ = v_node_4944_;
                            v_x_4933_ = v___x_4945_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4947_ = 0;
                            return v___x_4947_;
                        }
                    }
                } else {
                    v_ks_4948_ = leanh::lean_ctor_get(v_x_4932_, 0);
                    v___x_4949_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4950_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_ks_4948_, v___x_4949_, v_x_4934_);
                    return v___x_4950_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg___boxed(
    mut v_x_4951_: *mut leanh::LeanObject,
    mut v_x_4952_: *mut leanh::LeanObject,
    mut v_x_4953_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_23544__boxed_4954_: usize = 0;
    let mut v_res_4955_: u8 = 0;
    let mut v_r_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_23544__boxed_4954_ = leanh::lean_unbox_usize(v_x_4952_);
    leanh::lean_dec(v_x_4952_);
    v_res_4955_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_4951_, v_x_23544__boxed_4954_, v_x_4953_);
    leanh::lean_dec_ref(v_x_4953_);
    leanh::lean_dec_ref(v_x_4951_);
    v_r_4956_ = leanh::lean_box((v_res_4955_) as usize);
    return v_r_4956_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(
    mut v_x_4957_: *mut leanh::LeanObject,
    mut v_x_4958_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_4959_: u64 = 0;
    let mut v___x_4960_: usize = 0;
    let mut v___x_4961_: u8 = 0;
    v___x_4959_ = l_Lean_instHashableExtraModUse_hash(v_x_4958_);
    v___x_4960_ = lean_uint64_to_usize(v___x_4959_);
    v___x_4961_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_4957_, v___x_4960_, v_x_4958_);
    return v___x_4961_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg___boxed(
    mut v_x_4962_: *mut leanh::LeanObject,
    mut v_x_4963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4964_: u8 = 0;
    let mut v_r_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4964_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_4962_, v_x_4963_);
    leanh::lean_dec_ref(v_x_4963_);
    leanh::lean_dec_ref(v_x_4962_);
    v_r_4965_ = leanh::lean_box((v_res_4964_) as usize);
    return v_r_4965_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4968_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__1;
    v___x_4969_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__0;
    v___x_4970_ = l_Lean_PersistentHashMap_empty(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_4969_,
        v___x_4968_,
    );
    return v___x_4970_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4975_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__5;
    v___x_4976_ = l_Lean_stringToMessageData(v___x_4975_);
    return v___x_4976_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4978_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__7;
    v___x_4979_ = l_Lean_stringToMessageData(v___x_4978_);
    return v___x_4979_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4980_ = l_Lean_Elab_Command_mkUnexpander___closed__54;
    v___x_4981_ = l_Lean_stringToMessageData(v___x_4980_);
    return v___x_4981_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10()
-> *mut leanh::LeanObject {
    let mut v_cls_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cls_4982_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4;
    v___x_4983_ = l_Lean_Options_set___at___00Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6_spec__13___closed__1;
    v___x_4984_ = l_Lean_Name_append(v___x_4983_, v_cls_4982_);
    return v___x_4984_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4986_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__11;
    v___x_4987_ = l_Lean_stringToMessageData(v___x_4986_);
    return v___x_4987_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__13;
    v___x_4990_ = l_Lean_stringToMessageData(v___x_4989_);
    return v___x_4990_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(
    mut v_mod_4995_: *mut leanh::LeanObject,
    mut v_isMeta_4996_: u8,
    mut v_hint_4997_: *mut leanh::LeanObject,
    mut v___y_4998_: *mut leanh::LeanObject,
    mut v___y_4999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_5003_: u8 = 0;
    let mut v___x_5004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_5007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_5014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5028_: u8 = 0;
    let mut v_asyncMode_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5037_: u8 = 0;
    let mut v___x_5038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5047_: u8 = 0;
    let mut v_cls_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: u8 = 0;
    let mut v___x_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: u8 = 0;
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5001_ = lean_st_ref_get(v___y_4999_);
                v_env_5002_ = leanh::lean_ctor_get(v___x_5001_, 0);
                leanh::lean_inc_ref(v_env_5002_);
                leanh::lean_dec(v___x_5001_);
                v_isExporting_5003_ = leanh::lean_ctor_get_uint8(
                    v_env_5002_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                );
                leanh::lean_dec_ref(v_env_5002_);
                v___x_5004_ = lean_st_ref_get(v___y_4999_);
                v_env_5005_ = leanh::lean_ctor_get(v___x_5004_, 0);
                leanh::lean_inc_ref(v_env_5005_);
                leanh::lean_dec(v___x_5004_);
                v___x_5006_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__2);
                leanh::lean_inc(v_mod_4995_);
                v_entry_5007_ = leanh::lean_alloc_ctor(0, 1, (2) as u32);
                leanh::lean_ctor_set(v_entry_5007_, 0, v_mod_4995_);
                leanh::lean_ctor_set_uint8(
                    v_entry_5007_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v_isExporting_5003_,
                );
                leanh::lean_ctor_set_uint8(
                    v_entry_5007_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4996_,
                );
                v___x_5008_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_5009_ = leanh::lean_box(1);
                v___x_5010_ = leanh::lean_box(0);
                v___x_5038_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_5006_,
                    v___x_5008_,
                    v_env_5005_,
                    v___x_5009_,
                    v___x_5010_,
                );
                v___x_5039_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v___x_5038_, v_entry_5007_);
                leanh::lean_dec(v___x_5038_);
                if v___x_5039_ == 0 {
                    v___x_5040_ = l_Lean_inheritedTraceOptions;
                    v___x_5041_ = lean_st_ref_get(v___x_5040_);
                    v___x_5042_ = lean_st_ref_get(v___y_4999_);
                    v_scopes_5043_ = leanh::lean_ctor_get(v___x_5042_, 2);
                    leanh::lean_inc(v_scopes_5043_);
                    leanh::lean_dec(v___x_5042_);
                    v___x_5044_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_5045_ = l_List_head_x21___redArg(v___x_5044_, v_scopes_5043_);
                    leanh::lean_dec(v_scopes_5043_);
                    v_opts_5046_ = leanh::lean_ctor_get(v___x_5045_, 1);
                    leanh::lean_inc_ref(v_opts_5046_);
                    leanh::lean_dec(v___x_5045_);
                    v_hasTrace_5047_ = leanh::lean_ctor_get_uint8(
                        v_opts_5046_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5047_ == 0 {
                        leanh::lean_dec_ref(v_opts_5046_);
                        leanh::lean_dec(v___x_5041_);
                        leanh::lean_dec(v_hint_4997_);
                        leanh::lean_dec(v_mod_4995_);
                        v___y_5012_ = v___y_4999_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_5048_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__4;
                        v___x_5068_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__10);
                        v___x_5069_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_5041_,
                            v_opts_5046_,
                            v___x_5068_,
                        );
                        leanh::lean_dec_ref(v_opts_5046_);
                        leanh::lean_dec(v___x_5041_);
                        if v___x_5069_ == 0 {
                            leanh::lean_dec(v_hint_4997_);
                            leanh::lean_dec(v_mod_4995_);
                            v___y_5012_ = v___y_4999_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5070_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__12);
                            if v_isExporting_5003_ == 0 {
                                v___x_5079_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__17;
                                v___y_5072_ = v___x_5079_;
                                state = 6;
                                continue;
                            } else {
                                v___x_5080_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__18;
                                v___y_5072_ = v___x_5080_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref_known(v_entry_5007_, 1);
                    leanh::lean_dec(v_hint_4997_);
                    leanh::lean_dec(v_mod_4995_);
                    v___x_5081_ = leanh::lean_box(0);
                    v___x_5082_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5082_, 0, v___x_5081_);
                    return v___x_5082_;
                }
            }
            1 => {
                v___x_5013_ = lean_st_ref_take(v___y_5012_);
                v_toEnvExtension_5014_ = leanh::lean_ctor_get(v___x_5008_, 0);
                v_env_5015_ = leanh::lean_ctor_get(v___x_5013_, 0);
                v_messages_5016_ = leanh::lean_ctor_get(v___x_5013_, 1);
                v_scopes_5017_ = leanh::lean_ctor_get(v___x_5013_, 2);
                v_usedQuotCtxts_5018_ = leanh::lean_ctor_get(v___x_5013_, 3);
                v_nextMacroScope_5019_ = leanh::lean_ctor_get(v___x_5013_, 4);
                v_maxRecDepth_5020_ = leanh::lean_ctor_get(v___x_5013_, 5);
                v_ngen_5021_ = leanh::lean_ctor_get(v___x_5013_, 6);
                v_auxDeclNGen_5022_ = leanh::lean_ctor_get(v___x_5013_, 7);
                v_infoState_5023_ = leanh::lean_ctor_get(v___x_5013_, 8);
                v_traceState_5024_ = leanh::lean_ctor_get(v___x_5013_, 9);
                v_snapshotTasks_5025_ = leanh::lean_ctor_get(v___x_5013_, 10);
                v_isSharedCheck_5037_ = (!leanh::lean_is_exclusive(v___x_5013_)) as u8;
                if v_isSharedCheck_5037_ == 0 {
                    v___x_5027_ = v___x_5013_;
                    v_isShared_5028_ = v_isSharedCheck_5037_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_5025_);
                    leanh::lean_inc(v_traceState_5024_);
                    leanh::lean_inc(v_infoState_5023_);
                    leanh::lean_inc(v_auxDeclNGen_5022_);
                    leanh::lean_inc(v_ngen_5021_);
                    leanh::lean_inc(v_maxRecDepth_5020_);
                    leanh::lean_inc(v_nextMacroScope_5019_);
                    leanh::lean_inc(v_usedQuotCtxts_5018_);
                    leanh::lean_inc(v_scopes_5017_);
                    leanh::lean_inc(v_messages_5016_);
                    leanh::lean_inc(v_env_5015_);
                    leanh::lean_dec(v___x_5013_);
                    v___x_5027_ = leanh::lean_box(0);
                    v_isShared_5028_ = v_isSharedCheck_5037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_5029_ = leanh::lean_ctor_get(v_toEnvExtension_5014_, 2);
                v___x_5030_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_5008_,
                    v_env_5015_,
                    v_entry_5007_,
                    v_asyncMode_5029_,
                    v___x_5010_,
                );
                if v_isShared_5028_ == 0 {
                    leanh::lean_ctor_set(v___x_5027_, 0, v___x_5030_);
                    v___x_5032_ = v___x_5027_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5036_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 0, v___x_5030_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 1, v_messages_5016_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 2, v_scopes_5017_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 3, v_usedQuotCtxts_5018_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 4, v_nextMacroScope_5019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 5, v_maxRecDepth_5020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 6, v_ngen_5021_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 7, v_auxDeclNGen_5022_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 8, v_infoState_5023_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 9, v_traceState_5024_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 10, v_snapshotTasks_5025_);
                    v___x_5032_ = v_reuseFailAlloc_5036_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5033_ = lean_st_ref_set(v___y_5012_, v___x_5032_);
                v___x_5034_ = leanh::lean_box(0);
                v___x_5035_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5035_, 0, v___x_5034_);
                return v___x_5035_;
            }
            4 => {
                v___x_5052_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5052_, 0, v___y_5050_);
                leanh::lean_ctor_set(v___x_5052_, 1, v___y_5051_);
                v___x_5053_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1(v_cls_5048_, v___x_5052_, v___y_4998_, v___y_4999_);
                if leanh::lean_obj_tag(v___x_5053_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5053_, 1);
                    v___y_5012_ = v___y_4999_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_entry_5007_, 1);
                    return v___x_5053_;
                }
            }
            5 => {
                leanh::lean_inc_ref(v___y_5056_);
                v___x_5057_ = l_Lean_stringToMessageData(v___y_5056_);
                v___x_5058_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5058_, 0, v___y_5055_);
                leanh::lean_ctor_set(v___x_5058_, 1, v___x_5057_);
                v___x_5059_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__6);
                v___x_5060_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5060_, 0, v___x_5058_);
                leanh::lean_ctor_set(v___x_5060_, 1, v___x_5059_);
                v___x_5061_ = l_Lean_MessageData_ofName(v_mod_4995_);
                v___x_5062_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5062_, 0, v___x_5060_);
                leanh::lean_ctor_set(v___x_5062_, 1, v___x_5061_);
                v___x_5063_ = l_Lean_Name_isAnonymous(v_hint_4997_);
                if v___x_5063_ == 0 {
                    v___x_5064_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__8);
                    v___x_5065_ = l_Lean_MessageData_ofName(v_hint_4997_);
                    v___x_5066_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5066_, 0, v___x_5064_);
                    leanh::lean_ctor_set(v___x_5066_, 1, v___x_5065_);
                    v___y_5050_ = v___x_5062_;
                    v___y_5051_ = v___x_5066_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_hint_4997_);
                    v___x_5067_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__9);
                    v___y_5050_ = v___x_5062_;
                    v___y_5051_ = v___x_5067_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v___y_5072_);
                v___x_5073_ = l_Lean_stringToMessageData(v___y_5072_);
                v___x_5074_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5074_, 0, v___x_5070_);
                leanh::lean_ctor_set(v___x_5074_, 1, v___x_5073_);
                v___x_5075_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__14);
                v___x_5076_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5076_, 0, v___x_5074_);
                leanh::lean_ctor_set(v___x_5076_, 1, v___x_5075_);
                if v_isMeta_4996_ == 0 {
                    v___x_5077_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__15;
                    v___y_5055_ = v___x_5076_;
                    v___y_5056_ = v___x_5077_;
                    state = 5;
                    continue;
                } else {
                    v___x_5078_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___closed__16;
                    v___y_5055_ = v___x_5076_;
                    v___y_5056_ = v___x_5078_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6___boxed(
    mut v_mod_5083_: *mut leanh::LeanObject,
    mut v_isMeta_5084_: *mut leanh::LeanObject,
    mut v_hint_5085_: *mut leanh::LeanObject,
    mut v___y_5086_: *mut leanh::LeanObject,
    mut v___y_5087_: *mut leanh::LeanObject,
    mut v___y_5088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_5089_: u8 = 0;
    let mut v_res_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5089_ = (leanh::lean_unbox(v_isMeta_5084_) as u8);
    v_res_5090_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_mod_5083_, v_isMeta_boxed_5089_, v_hint_5085_, v___y_5086_, v___y_5087_);
    leanh::lean_dec(v___y_5087_);
    leanh::lean_dec_ref(v___y_5086_);
    return v_res_5090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(
    mut v___x_5091_: *mut leanh::LeanObject,
    mut v_declName_5092_: *mut leanh::LeanObject,
    mut v_as_5093_: *mut leanh::LeanObject,
    mut v_sz_5094_: usize,
    mut v_i_5095_: usize,
    mut v_b_5096_: *mut leanh::LeanObject,
    mut v___y_5097_: *mut leanh::LeanObject,
    mut v___y_5098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5100_: u8 = 0;
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: u8 = 0;
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: usize = 0;
    let mut v___x_5113_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5100_ = lean_usize_dec_lt(v_i_5095_, v_sz_5094_);
                if v___x_5100_ == 0 {
                    leanh::lean_dec(v_declName_5092_);
                    v___x_5101_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5101_, 0, v_b_5096_);
                    return v___x_5101_;
                } else {
                    v___x_5102_ = l_Lean_Environment_header(v___x_5091_);
                    v_modules_5103_ = leanh::lean_ctor_get(v___x_5102_, 3);
                    leanh::lean_inc_ref(v_modules_5103_);
                    leanh::lean_dec_ref(v___x_5102_);
                    v___x_5104_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_5105_ = lean_array_uget_borrowed(v_as_5093_, v_i_5095_);
                    v___x_5106_ = lean_array_get(v___x_5104_, v_modules_5103_, v_a_5105_);
                    leanh::lean_dec_ref(v_modules_5103_);
                    v_toImport_5107_ = leanh::lean_ctor_get(v___x_5106_, 0);
                    leanh::lean_inc_ref(v_toImport_5107_);
                    leanh::lean_dec(v___x_5106_);
                    v_module_5108_ = leanh::lean_ctor_get(v_toImport_5107_, 0);
                    leanh::lean_inc(v_module_5108_);
                    leanh::lean_dec_ref(v_toImport_5107_);
                    v___x_5109_ = 0;
                    leanh::lean_inc(v_declName_5092_);
                    v___x_5110_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_5108_, v___x_5109_, v_declName_5092_, v___y_5097_, v___y_5098_);
                    if leanh::lean_obj_tag(v___x_5110_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5110_, 1);
                        v___x_5111_ = leanh::lean_box(0);
                        v___x_5112_ = 1usize;
                        v___x_5113_ = lean_usize_add(v_i_5095_, v___x_5112_);
                        v_i_5095_ = v___x_5113_;
                        v_b_5096_ = v___x_5111_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_declName_5092_);
                        return v___x_5110_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7___boxed(
    mut v___x_5115_: *mut leanh::LeanObject,
    mut v_declName_5116_: *mut leanh::LeanObject,
    mut v_as_5117_: *mut leanh::LeanObject,
    mut v_sz_5118_: *mut leanh::LeanObject,
    mut v_i_5119_: *mut leanh::LeanObject,
    mut v_b_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
    mut v___y_5122_: *mut leanh::LeanObject,
    mut v___y_5123_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5124_: usize = 0;
    let mut v_i_boxed_5125_: usize = 0;
    let mut v_res_5126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5124_ = leanh::lean_unbox_usize(v_sz_5118_);
    leanh::lean_dec(v_sz_5118_);
    v_i_boxed_5125_ = leanh::lean_unbox_usize(v_i_5119_);
    leanh::lean_dec(v_i_5119_);
    v_res_5126_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v___x_5115_, v_declName_5116_, v_as_5117_, v_sz_boxed_5124_, v_i_boxed_5125_, v_b_5120_, v___y_5121_, v___y_5122_);
    leanh::lean_dec(v___y_5122_);
    leanh::lean_dec_ref(v___y_5121_);
    leanh::lean_dec_ref(v_as_5117_);
    leanh::lean_dec_ref(v___x_5115_);
    return v_res_5126_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(
    mut v_a_5127_: *mut leanh::LeanObject,
    mut v_x_5128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: u8 = 0;
    let mut v___x_5135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5128_) == 0 {
                    v___x_5129_ = leanh::lean_box(0);
                    return v___x_5129_;
                } else {
                    v_key_5130_ = leanh::lean_ctor_get(v_x_5128_, 0);
                    v_value_5131_ = leanh::lean_ctor_get(v_x_5128_, 1);
                    v_tail_5132_ = leanh::lean_ctor_get(v_x_5128_, 2);
                    v___x_5133_ = lean_name_eq(v_key_5130_, v_a_5127_);
                    if v___x_5133_ == 0 {
                        v_x_5128_ = v_tail_5132_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_5131_);
                        v___x_5135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5135_, 0, v_value_5131_);
                        return v___x_5135_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg___boxed(
    mut v_a_5136_: *mut leanh::LeanObject,
    mut v_x_5137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5138_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_5136_, v_x_5137_);
    leanh::lean_dec(v_x_5137_);
    leanh::lean_dec(v_a_5136_);
    return v_res_5138_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0()
-> u64 {
    let mut v___x_5139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: u64 = 0;
    v___x_5139_ = leanh::lean_unsigned_to_nat(1723);
    v___x_5140_ = lean_uint64_of_nat(v___x_5139_);
    return v___x_5140_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(
    mut v_m_5141_: *mut leanh::LeanObject,
    mut v_a_5142_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5146_: u64 = 0;
    let mut v___x_5147_: u64 = 0;
    let mut v___x_5148_: u64 = 0;
    let mut v_fold_5149_: u64 = 0;
    let mut v___x_5150_: u64 = 0;
    let mut v___x_5151_: u64 = 0;
    let mut v___x_5152_: u64 = 0;
    let mut v___x_5153_: usize = 0;
    let mut v___x_5154_: usize = 0;
    let mut v___x_5155_: usize = 0;
    let mut v___x_5156_: usize = 0;
    let mut v___x_5157_: usize = 0;
    let mut v___x_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: u64 = 0;
    let mut v_hash_5161_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5143_ = leanh::lean_ctor_get(v_m_5141_, 1);
                v___x_5144_ = lean_array_get_size(v_buckets_5143_);
                if leanh::lean_obj_tag(v_a_5142_) == 0 {
                    v___x_5160_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___closed__0);
                    v___y_5146_ = v___x_5160_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5161_ = leanh::lean_ctor_get_uint64(
                        v_a_5142_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5146_ = v_hash_5161_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5147_ = 32u64;
                v___x_5148_ = lean_uint64_shift_right(v___y_5146_, v___x_5147_);
                v_fold_5149_ = lean_uint64_xor(v___y_5146_, v___x_5148_);
                v___x_5150_ = 16u64;
                v___x_5151_ = lean_uint64_shift_right(v_fold_5149_, v___x_5150_);
                v___x_5152_ = lean_uint64_xor(v_fold_5149_, v___x_5151_);
                v___x_5153_ = lean_uint64_to_usize(v___x_5152_);
                v___x_5154_ = lean_usize_of_nat(v___x_5144_);
                v___x_5155_ = 1usize;
                v___x_5156_ = lean_usize_sub(v___x_5154_, v___x_5155_);
                v___x_5157_ = lean_usize_land(v___x_5153_, v___x_5156_);
                v___x_5158_ = lean_array_uget_borrowed(v_buckets_5143_, v___x_5157_);
                v___x_5159_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_5142_, v___x_5158_);
                return v___x_5159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg___boxed(
    mut v_m_5162_: *mut leanh::LeanObject,
    mut v_a_5163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5164_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_5162_, v_a_5163_);
    leanh::lean_dec(v_a_5163_);
    leanh::lean_dec_ref(v_m_5162_);
    return v_res_5164_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5167_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__1;
    v___x_5168_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__0;
    v___x_5169_ = l_Std_HashMap_instInhabited(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_5168_,
        v___x_5167_,
    );
    return v___x_5169_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(
    mut v_declName_5172_: *mut leanh::LeanObject,
    mut v_isMeta_5173_: u8,
    mut v___y_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5185_: usize = 0;
    let mut v___x_5186_: usize = 0;
    let mut v___x_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut v_unused_5195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: u8 = 0;
    let mut v___x_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5207_: u8 = 0;
    let mut v_toImport_5208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5218_: u8 = 0;
    let mut v___x_5219_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5177_ = lean_st_ref_get(v___y_5175_);
                v_env_5181_ = leanh::lean_ctor_get(v___x_5177_, 0);
                leanh::lean_inc_ref(v_env_5181_);
                leanh::lean_dec(v___x_5177_);
                v___x_5196_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5181_, v_declName_5172_);
                if leanh::lean_obj_tag(v___x_5196_) == 0 {
                    leanh::lean_dec_ref(v_env_5181_);
                    leanh::lean_dec(v_declName_5172_);
                    state = 1;
                    continue;
                } else {
                    v_val_5197_ = leanh::lean_ctor_get(v___x_5196_, 0);
                    leanh::lean_inc(v_val_5197_);
                    leanh::lean_dec_ref_known(v___x_5196_, 1);
                    v___x_5198_ = l_Lean_Environment_header(v_env_5181_);
                    v_modules_5199_ = leanh::lean_ctor_get(v___x_5198_, 3);
                    leanh::lean_inc_ref(v_modules_5199_);
                    leanh::lean_dec_ref(v___x_5198_);
                    v___x_5200_ = lean_array_get_size(v_modules_5199_);
                    v___x_5201_ = lean_nat_dec_lt(v_val_5197_, v___x_5200_);
                    if v___x_5201_ == 0 {
                        leanh::lean_dec_ref(v_modules_5199_);
                        leanh::lean_dec(v_val_5197_);
                        leanh::lean_dec_ref(v_env_5181_);
                        leanh::lean_dec(v_declName_5172_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5202_ = lean_st_ref_get(v___y_5175_);
                        v_env_5203_ = leanh::lean_ctor_get(v___x_5202_, 0);
                        leanh::lean_inc_ref(v_env_5203_);
                        leanh::lean_dec(v___x_5202_);
                        v___x_5204_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__2);
                        v___x_5205_ = lean_array_fget(v_modules_5199_, v_val_5197_);
                        leanh::lean_dec(v_val_5197_);
                        leanh::lean_dec_ref(v_modules_5199_);
                        if v_isMeta_5173_ == 0 {
                            leanh::lean_dec_ref(v_env_5203_);
                            v___y_5207_ = v_isMeta_5173_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_declName_5172_);
                            v___x_5218_ = l_Lean_isMarkedMeta(v_env_5203_, v_declName_5172_);
                            if v___x_5218_ == 0 {
                                v___y_5207_ = v_isMeta_5173_;
                                state = 5;
                                continue;
                            } else {
                                v___x_5219_ = 0;
                                v___y_5207_ = v___x_5219_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5179_ = leanh::lean_box(0);
                v___x_5180_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5180_, 0, v___x_5179_);
                return v___x_5180_;
            }
            2 => {
                v___x_5184_ = leanh::lean_box(0);
                v_sz_5185_ = lean_array_size(v___y_5183_);
                v___x_5186_ = 0usize;
                v___x_5187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__7(v_env_5181_, v_declName_5172_, v___y_5183_, v_sz_5185_, v___x_5186_, v___x_5184_, v___y_5174_, v___y_5175_);
                leanh::lean_dec_ref(v___y_5183_);
                leanh::lean_dec_ref(v_env_5181_);
                if leanh::lean_obj_tag(v___x_5187_) == 0 {
                    v_isSharedCheck_5194_ = (!leanh::lean_is_exclusive(v___x_5187_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v_unused_5195_ = leanh::lean_ctor_get(v___x_5187_, 0);
                        leanh::lean_dec(v_unused_5195_);
                        v___x_5189_ = v___x_5187_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5187_);
                        v___x_5189_ = leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_5187_;
                }
            }
            3 => {
                if v_isShared_5190_ == 0 {
                    leanh::lean_ctor_set(v___x_5189_, 0, v___x_5184_);
                    v___x_5192_ = v___x_5189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v___x_5184_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5192_;
            }
            5 => {
                v_toImport_5208_ = leanh::lean_ctor_get(v___x_5205_, 0);
                leanh::lean_inc_ref(v_toImport_5208_);
                leanh::lean_dec(v___x_5205_);
                v_module_5209_ = leanh::lean_ctor_get(v_toImport_5208_, 0);
                leanh::lean_inc(v_module_5209_);
                leanh::lean_dec_ref(v_toImport_5208_);
                leanh::lean_inc(v_declName_5172_);
                v___x_5210_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6(v_module_5209_, v___y_5207_, v_declName_5172_, v___y_5174_, v___y_5175_);
                if leanh::lean_obj_tag(v___x_5210_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5210_, 1);
                    v___x_5211_ = l_Lean_indirectModUseExt;
                    v___x_5212_ = leanh::lean_box(1);
                    v___x_5213_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_5181_);
                    v___x_5214_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_5204_,
                        v___x_5211_,
                        v_env_5181_,
                        v___x_5212_,
                        v___x_5213_,
                    );
                    v___x_5215_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v___x_5214_, v_declName_5172_);
                    leanh::lean_dec(v___x_5214_);
                    if leanh::lean_obj_tag(v___x_5215_) == 0 {
                        v___x_5216_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___closed__3;
                        v___y_5183_ = v___x_5216_;
                        state = 2;
                        continue;
                    } else {
                        v_val_5217_ = leanh::lean_ctor_get(v___x_5215_, 0);
                        leanh::lean_inc(v_val_5217_);
                        leanh::lean_dec_ref_known(v___x_5215_, 1);
                        v___y_5183_ = v_val_5217_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_env_5181_);
                    leanh::lean_dec(v_declName_5172_);
                    return v___x_5210_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3___boxed(
    mut v_declName_5220_: *mut leanh::LeanObject,
    mut v_isMeta_5221_: *mut leanh::LeanObject,
    mut v___y_5222_: *mut leanh::LeanObject,
    mut v___y_5223_: *mut leanh::LeanObject,
    mut v___y_5224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isMeta_boxed_5225_: u8 = 0;
    let mut v_res_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5225_ = (leanh::lean_unbox(v_isMeta_5221_) as u8);
    v_res_5226_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_declName_5220_, v_isMeta_boxed_5225_, v___y_5222_, v___y_5223_);
    leanh::lean_dec(v___y_5223_);
    leanh::lean_dec_ref(v___y_5222_);
    return v_res_5226_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(
    mut v_as_x27_5227_: *mut leanh::LeanObject,
    mut v_b_5228_: *mut leanh::LeanObject,
    mut v___y_5229_: *mut leanh::LeanObject,
    mut v___y_5230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: u8 = 0;
    let mut v___x_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_as_x27_5227_) == 0 {
                    v___x_5232_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5232_, 0, v_b_5228_);
                    return v___x_5232_;
                } else {
                    v_head_5233_ = leanh::lean_ctor_get(v_as_x27_5227_, 0);
                    v_tail_5234_ = leanh::lean_ctor_get(v_as_x27_5227_, 1);
                    v___x_5235_ = 1;
                    leanh::lean_inc(v_head_5233_);
                    v___x_5236_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3(v_head_5233_, v___x_5235_, v___y_5229_, v___y_5230_);
                    if leanh::lean_obj_tag(v___x_5236_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5236_, 1);
                        v___x_5237_ = leanh::lean_box(0);
                        v_as_x27_5227_ = v_tail_5234_;
                        v_b_5228_ = v___x_5237_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5236_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg___boxed(
    mut v_as_x27_5239_: *mut leanh::LeanObject,
    mut v_b_5240_: *mut leanh::LeanObject,
    mut v___y_5241_: *mut leanh::LeanObject,
    mut v___y_5242_: *mut leanh::LeanObject,
    mut v___y_5243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5244_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_5239_, v_b_5240_, v___y_5241_, v___y_5242_);
    leanh::lean_dec(v___y_5242_);
    leanh::lean_dec_ref(v___y_5241_);
    leanh::lean_dec(v_as_x27_5239_);
    return v_res_5244_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(
    mut v_x_5246_: *mut leanh::LeanObject,
    mut v___y_5247_: *mut leanh::LeanObject,
    mut v___y_5248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_5287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5305_: u8 = 0;
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5313_: u8 = 0;
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5317_: u8 = 0;
    let mut v_unused_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5322_: u8 = 0;
    let mut v___x_5324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5326_: u8 = 0;
    let mut v_reuseFailAlloc_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_unused_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5337_: u8 = 0;
    let mut v_a_5338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: u8 = 0;
    let mut v___x_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5354_: u8 = 0;
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5358_: u8 = 0;
    let mut v_a_5359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5362_: u8 = 0;
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5366_: u8 = 0;
    let mut v_a_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5370_: u8 = 0;
    let mut v___x_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5374_: u8 = 0;
    let mut v_a_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5378_: u8 = 0;
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5250_ = lean_st_ref_get(v___y_5248_);
                v_env_5251_ = leanh::lean_ctor_get(v___x_5250_, 0);
                leanh::lean_inc_ref(v_env_5251_);
                leanh::lean_dec(v___x_5250_);
                v___x_5252_ = lean_st_ref_get(v___y_5248_);
                v_scopes_5253_ = leanh::lean_ctor_get(v___x_5252_, 2);
                leanh::lean_inc(v_scopes_5253_);
                leanh::lean_dec(v___x_5252_);
                v___x_5254_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_5255_ = l_List_head_x21___redArg(v___x_5254_, v_scopes_5253_);
                leanh::lean_dec(v_scopes_5253_);
                v_opts_5256_ = leanh::lean_ctor_get(v___x_5255_, 1);
                leanh::lean_inc_ref(v_opts_5256_);
                leanh::lean_dec(v___x_5255_);
                v___x_5257_ = l_Lean_Elab_Command_getScope___redArg(v___y_5248_);
                if leanh::lean_obj_tag(v___x_5257_) == 0 {
                    v_a_5258_ = leanh::lean_ctor_get(v___x_5257_, 0);
                    leanh::lean_inc(v_a_5258_);
                    leanh::lean_dec_ref_known(v___x_5257_, 1);
                    v_currNamespace_5259_ = leanh::lean_ctor_get(v_a_5258_, 2);
                    leanh::lean_inc(v_currNamespace_5259_);
                    leanh::lean_dec(v_a_5258_);
                    v___x_5260_ = l_Lean_Elab_Command_getScope___redArg(v___y_5248_);
                    if leanh::lean_obj_tag(v___x_5260_) == 0 {
                        v_a_5261_ = leanh::lean_ctor_get(v___x_5260_, 0);
                        leanh::lean_inc(v_a_5261_);
                        leanh::lean_dec_ref_known(v___x_5260_, 1);
                        v_openDecls_5262_ = leanh::lean_ctor_get(v_a_5261_, 3);
                        leanh::lean_inc(v_openDecls_5262_);
                        leanh::lean_dec(v_a_5261_);
                        v___x_5263_ = l_Lean_Elab_Command_getRef___redArg(v___y_5247_);
                        if leanh::lean_obj_tag(v___x_5263_) == 0 {
                            v_a_5264_ = leanh::lean_ctor_get(v___x_5263_, 0);
                            leanh::lean_inc(v_a_5264_);
                            leanh::lean_dec_ref_known(v___x_5263_, 1);
                            v___x_5265_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5247_);
                            if leanh::lean_obj_tag(v___x_5265_) == 0 {
                                v_a_5266_ = leanh::lean_ctor_get(v___x_5265_, 0);
                                leanh::lean_inc(v_a_5266_);
                                leanh::lean_dec_ref_known(v___x_5265_, 1);
                                v_currRecDepth_5267_ = leanh::lean_ctor_get(v___y_5247_, 2);
                                v_quotContext_x3f_5268_ =
                                    leanh::lean_ctor_get(v___y_5247_, 5);
                                leanh::lean_inc_ref_n(v_env_5251_, 3);
                                v___f_5269_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                                leanh::lean_closure_set(v___f_5269_, 0, v_env_5251_);
                                v___f_5270_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                                leanh::lean_closure_set(v___f_5270_, 0, v_env_5251_);
                                leanh::lean_inc_n(v_currNamespace_5259_, 2);
                                v___f_5271_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                                leanh::lean_closure_set(
                                    v___f_5271_,
                                    0,
                                    v_currNamespace_5259_,
                                );
                                leanh::lean_inc(v_openDecls_5262_);
                                v___f_5272_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                                leanh::lean_closure_set(v___f_5272_, 0, v_env_5251_);
                                leanh::lean_closure_set(
                                    v___f_5272_,
                                    1,
                                    v_currNamespace_5259_,
                                );
                                leanh::lean_closure_set(v___f_5272_, 2, v_openDecls_5262_);
                                v___f_5273_ = leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                                leanh::lean_closure_set(v___f_5273_, 0, v_env_5251_);
                                leanh::lean_closure_set(v___f_5273_, 1, v_opts_5256_);
                                leanh::lean_closure_set(
                                    v___f_5273_,
                                    2,
                                    v_currNamespace_5259_,
                                );
                                leanh::lean_closure_set(v___f_5273_, 3, v_openDecls_5262_);
                                v_methods_5274_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                leanh::lean_ctor_set(v_methods_5274_, 0, v___f_5270_);
                                leanh::lean_ctor_set(v_methods_5274_, 1, v___f_5271_);
                                leanh::lean_ctor_set(v_methods_5274_, 2, v___f_5269_);
                                leanh::lean_ctor_set(v_methods_5274_, 3, v___f_5272_);
                                leanh::lean_ctor_set(v_methods_5274_, 4, v___f_5273_);
                                if leanh::lean_obj_tag(v_quotContext_x3f_5268_) == 0 {
                                    v___x_5348_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_5248_);
                                    v_a_5349_ = leanh::lean_ctor_get(v___x_5348_, 0);
                                    leanh::lean_inc(v_a_5349_);
                                    leanh::lean_dec_ref(v___x_5348_);
                                    v_a_5276_ = v_a_5349_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_5350_ =
                                        leanh::lean_ctor_get(v_quotContext_x3f_5268_, 0);
                                    leanh::lean_inc(v_val_5350_);
                                    v_a_5276_ = v_val_5350_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5264_);
                                leanh::lean_dec(v_openDecls_5262_);
                                leanh::lean_dec(v_currNamespace_5259_);
                                leanh::lean_dec_ref(v_opts_5256_);
                                leanh::lean_dec_ref(v_env_5251_);
                                leanh::lean_dec_ref(v_x_5246_);
                                v_a_5351_ = leanh::lean_ctor_get(v___x_5265_, 0);
                                v_isSharedCheck_5358_ =
                                    (!leanh::lean_is_exclusive(v___x_5265_)) as u8;
                                if v_isSharedCheck_5358_ == 0 {
                                    v___x_5353_ = v___x_5265_;
                                    v_isShared_5354_ = v_isSharedCheck_5358_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5351_);
                                    leanh::lean_dec(v___x_5265_);
                                    v___x_5353_ = leanh::lean_box(0);
                                    v_isShared_5354_ = v_isSharedCheck_5358_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_openDecls_5262_);
                            leanh::lean_dec(v_currNamespace_5259_);
                            leanh::lean_dec_ref(v_opts_5256_);
                            leanh::lean_dec_ref(v_env_5251_);
                            leanh::lean_dec_ref(v_x_5246_);
                            v_a_5359_ = leanh::lean_ctor_get(v___x_5263_, 0);
                            v_isSharedCheck_5366_ =
                                (!leanh::lean_is_exclusive(v___x_5263_)) as u8;
                            if v_isSharedCheck_5366_ == 0 {
                                v___x_5361_ = v___x_5263_;
                                v_isShared_5362_ = v_isSharedCheck_5366_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5359_);
                                leanh::lean_dec(v___x_5263_);
                                v___x_5361_ = leanh::lean_box(0);
                                v_isShared_5362_ = v_isSharedCheck_5366_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_currNamespace_5259_);
                        leanh::lean_dec_ref(v_opts_5256_);
                        leanh::lean_dec_ref(v_env_5251_);
                        leanh::lean_dec_ref(v_x_5246_);
                        v_a_5367_ = leanh::lean_ctor_get(v___x_5260_, 0);
                        v_isSharedCheck_5374_ =
                            (!leanh::lean_is_exclusive(v___x_5260_)) as u8;
                        if v_isSharedCheck_5374_ == 0 {
                            v___x_5369_ = v___x_5260_;
                            v_isShared_5370_ = v_isSharedCheck_5374_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5367_);
                            leanh::lean_dec(v___x_5260_);
                            v___x_5369_ = leanh::lean_box(0);
                            v_isShared_5370_ = v_isSharedCheck_5374_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_opts_5256_);
                    leanh::lean_dec_ref(v_env_5251_);
                    leanh::lean_dec_ref(v_x_5246_);
                    v_a_5375_ = leanh::lean_ctor_get(v___x_5257_, 0);
                    v_isSharedCheck_5382_ = (!leanh::lean_is_exclusive(v___x_5257_)) as u8;
                    if v_isSharedCheck_5382_ == 0 {
                        v___x_5377_ = v___x_5257_;
                        v_isShared_5378_ = v_isSharedCheck_5382_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5375_);
                        leanh::lean_dec(v___x_5257_);
                        v___x_5377_ = leanh::lean_box(0);
                        v_isShared_5378_ = v_isSharedCheck_5382_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5277_ = lean_st_ref_get(v___y_5248_);
                v_maxRecDepth_5278_ = leanh::lean_ctor_get(v___x_5277_, 5);
                leanh::lean_inc(v_maxRecDepth_5278_);
                leanh::lean_dec(v___x_5277_);
                v___x_5279_ = lean_st_ref_get(v___y_5248_);
                v_nextMacroScope_5280_ = leanh::lean_ctor_get(v___x_5279_, 4);
                leanh::lean_inc(v_nextMacroScope_5280_);
                leanh::lean_dec(v___x_5279_);
                leanh::lean_inc(v_currRecDepth_5267_);
                v___x_5281_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_5281_, 0, v_methods_5274_);
                leanh::lean_ctor_set(v___x_5281_, 1, v_a_5276_);
                leanh::lean_ctor_set(v___x_5281_, 2, v_a_5266_);
                leanh::lean_ctor_set(v___x_5281_, 3, v_currRecDepth_5267_);
                leanh::lean_ctor_set(v___x_5281_, 4, v_maxRecDepth_5278_);
                leanh::lean_ctor_set(v___x_5281_, 5, v_a_5264_);
                v___x_5282_ = leanh::lean_box(0);
                v___x_5283_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5283_, 0, v_nextMacroScope_5280_);
                leanh::lean_ctor_set(v___x_5283_, 1, v___x_5282_);
                leanh::lean_ctor_set(v___x_5283_, 2, v___x_5282_);
                v___x_5284_ = leanh::lean_apply_2(v_x_5246_, v___x_5281_, v___x_5283_);
                if leanh::lean_obj_tag(v___x_5284_) == 0 {
                    v_a_5285_ = leanh::lean_ctor_get(v___x_5284_, 1);
                    leanh::lean_inc(v_a_5285_);
                    v_a_5286_ = leanh::lean_ctor_get(v___x_5284_, 0);
                    leanh::lean_inc(v_a_5286_);
                    leanh::lean_dec_ref_known(v___x_5284_, 2);
                    v_macroScope_5287_ = leanh::lean_ctor_get(v_a_5285_, 0);
                    leanh::lean_inc(v_macroScope_5287_);
                    v_traceMsgs_5288_ = leanh::lean_ctor_get(v_a_5285_, 1);
                    leanh::lean_inc(v_traceMsgs_5288_);
                    v_expandedMacroDecls_5289_ = leanh::lean_ctor_get(v_a_5285_, 2);
                    leanh::lean_inc(v_expandedMacroDecls_5289_);
                    leanh::lean_dec(v_a_5285_);
                    v___x_5290_ = leanh::lean_box(0);
                    v___x_5291_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_expandedMacroDecls_5289_, v___x_5290_, v___y_5247_, v___y_5248_);
                    leanh::lean_dec(v_expandedMacroDecls_5289_);
                    if leanh::lean_obj_tag(v___x_5291_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5291_, 1);
                        v___x_5292_ = lean_st_ref_take(v___y_5248_);
                        v_env_5293_ = leanh::lean_ctor_get(v___x_5292_, 0);
                        v_messages_5294_ = leanh::lean_ctor_get(v___x_5292_, 1);
                        v_scopes_5295_ = leanh::lean_ctor_get(v___x_5292_, 2);
                        v_usedQuotCtxts_5296_ = leanh::lean_ctor_get(v___x_5292_, 3);
                        v_maxRecDepth_5297_ = leanh::lean_ctor_get(v___x_5292_, 5);
                        v_ngen_5298_ = leanh::lean_ctor_get(v___x_5292_, 6);
                        v_auxDeclNGen_5299_ = leanh::lean_ctor_get(v___x_5292_, 7);
                        v_infoState_5300_ = leanh::lean_ctor_get(v___x_5292_, 8);
                        v_traceState_5301_ = leanh::lean_ctor_get(v___x_5292_, 9);
                        v_snapshotTasks_5302_ = leanh::lean_ctor_get(v___x_5292_, 10);
                        v_isSharedCheck_5328_ =
                            (!leanh::lean_is_exclusive(v___x_5292_)) as u8;
                        if v_isSharedCheck_5328_ == 0 {
                            v_unused_5329_ = leanh::lean_ctor_get(v___x_5292_, 4);
                            leanh::lean_dec(v_unused_5329_);
                            v___x_5304_ = v___x_5292_;
                            v_isShared_5305_ = v_isSharedCheck_5328_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_5302_);
                            leanh::lean_inc(v_traceState_5301_);
                            leanh::lean_inc(v_infoState_5300_);
                            leanh::lean_inc(v_auxDeclNGen_5299_);
                            leanh::lean_inc(v_ngen_5298_);
                            leanh::lean_inc(v_maxRecDepth_5297_);
                            leanh::lean_inc(v_usedQuotCtxts_5296_);
                            leanh::lean_inc(v_scopes_5295_);
                            leanh::lean_inc(v_messages_5294_);
                            leanh::lean_inc(v_env_5293_);
                            leanh::lean_dec(v___x_5292_);
                            v___x_5304_ = leanh::lean_box(0);
                            v_isShared_5305_ = v_isSharedCheck_5328_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_traceMsgs_5288_);
                        leanh::lean_dec(v_macroScope_5287_);
                        leanh::lean_dec(v_a_5286_);
                        v_a_5330_ = leanh::lean_ctor_get(v___x_5291_, 0);
                        v_isSharedCheck_5337_ =
                            (!leanh::lean_is_exclusive(v___x_5291_)) as u8;
                        if v_isSharedCheck_5337_ == 0 {
                            v___x_5332_ = v___x_5291_;
                            v_isShared_5333_ = v_isSharedCheck_5337_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5330_);
                            leanh::lean_dec(v___x_5291_);
                            v___x_5332_ = leanh::lean_box(0);
                            v_isShared_5333_ = v_isSharedCheck_5337_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_5338_ = leanh::lean_ctor_get(v___x_5284_, 0);
                    leanh::lean_inc(v_a_5338_);
                    leanh::lean_dec_ref_known(v___x_5284_, 2);
                    if leanh::lean_obj_tag(v_a_5338_) == 0 {
                        v_a_5339_ = leanh::lean_ctor_get(v_a_5338_, 0);
                        leanh::lean_inc(v_a_5339_);
                        v_a_5340_ = leanh::lean_ctor_get(v_a_5338_, 1);
                        leanh::lean_inc_ref(v_a_5340_);
                        leanh::lean_dec_ref_known(v_a_5338_, 2);
                        v___x_5341_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___closed__0;
                        v___x_5342_ = lean_string_dec_eq(v_a_5340_, v___x_5341_);
                        if v___x_5342_ == 0 {
                            v___x_5343_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5343_, 0, v_a_5340_);
                            v___x_5344_ = l_Lean_MessageData_ofFormat(v___x_5343_);
                            v___x_5345_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_a_5339_, v___x_5344_, v___y_5247_, v___y_5248_);
                            leanh::lean_dec(v_a_5339_);
                            return v___x_5345_;
                        } else {
                            leanh::lean_dec_ref(v_a_5340_);
                            v___x_5346_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_a_5339_);
                            return v___x_5346_;
                        }
                    } else {
                        v___x_5347_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                        return v___x_5347_;
                    }
                }
            }
            2 => {
                if v_isShared_5305_ == 0 {
                    leanh::lean_ctor_set(v___x_5304_, 4, v_macroScope_5287_);
                    v___x_5307_ = v___x_5304_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5327_ = leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_env_5293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_messages_5294_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 2, v_scopes_5295_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 3, v_usedQuotCtxts_5296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 4, v_macroScope_5287_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 5, v_maxRecDepth_5297_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 6, v_ngen_5298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 7, v_auxDeclNGen_5299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 8, v_infoState_5300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 9, v_traceState_5301_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 10, v_snapshotTasks_5302_);
                    v___x_5307_ = v_reuseFailAlloc_5327_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5308_ = lean_st_ref_set(v___y_5248_, v___x_5307_);
                v___x_5309_ = l_List_reverse___redArg(v_traceMsgs_5288_);
                v___x_5310_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__5(v___x_5309_, v___y_5247_, v___y_5248_);
                if leanh::lean_obj_tag(v___x_5310_) == 0 {
                    v_isSharedCheck_5317_ = (!leanh::lean_is_exclusive(v___x_5310_)) as u8;
                    if v_isSharedCheck_5317_ == 0 {
                        v_unused_5318_ = leanh::lean_ctor_get(v___x_5310_, 0);
                        leanh::lean_dec(v_unused_5318_);
                        v___x_5312_ = v___x_5310_;
                        v_isShared_5313_ = v_isSharedCheck_5317_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5310_);
                        v___x_5312_ = leanh::lean_box(0);
                        v_isShared_5313_ = v_isSharedCheck_5317_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_5286_);
                    v_a_5319_ = leanh::lean_ctor_get(v___x_5310_, 0);
                    v_isSharedCheck_5326_ = (!leanh::lean_is_exclusive(v___x_5310_)) as u8;
                    if v_isSharedCheck_5326_ == 0 {
                        v___x_5321_ = v___x_5310_;
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5319_);
                        leanh::lean_dec(v___x_5310_);
                        v___x_5321_ = leanh::lean_box(0);
                        v_isShared_5322_ = v_isSharedCheck_5326_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_5313_ == 0 {
                    leanh::lean_ctor_set(v___x_5312_, 0, v_a_5286_);
                    v___x_5315_ = v___x_5312_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5316_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5316_, 0, v_a_5286_);
                    v___x_5315_ = v_reuseFailAlloc_5316_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5315_;
            }
            6 => {
                if v_isShared_5322_ == 0 {
                    v___x_5324_ = v___x_5321_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5325_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v_a_5319_);
                    v___x_5324_ = v_reuseFailAlloc_5325_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5324_;
            }
            8 => {
                if v_isShared_5333_ == 0 {
                    v___x_5335_ = v___x_5332_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5336_, 0, v_a_5330_);
                    v___x_5335_ = v_reuseFailAlloc_5336_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5335_;
            }
            10 => {
                if v_isShared_5354_ == 0 {
                    v___x_5356_ = v___x_5353_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5357_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5357_, 0, v_a_5351_);
                    v___x_5356_ = v_reuseFailAlloc_5357_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5356_;
            }
            12 => {
                if v_isShared_5362_ == 0 {
                    v___x_5364_ = v___x_5361_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5365_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5365_, 0, v_a_5359_);
                    v___x_5364_ = v_reuseFailAlloc_5365_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5364_;
            }
            14 => {
                if v_isShared_5370_ == 0 {
                    v___x_5372_ = v___x_5369_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5373_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
                    v___x_5372_ = v_reuseFailAlloc_5373_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5372_;
            }
            16 => {
                if v_isShared_5378_ == 0 {
                    v___x_5380_ = v___x_5377_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5381_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
                    v___x_5380_ = v_reuseFailAlloc_5381_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg___boxed(
    mut v_x_5383_: *mut leanh::LeanObject,
    mut v___y_5384_: *mut leanh::LeanObject,
    mut v___y_5385_: *mut leanh::LeanObject,
    mut v___y_5386_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5387_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(
        v_x_5383_,
        v___y_5384_,
        v___y_5385_,
    );
    leanh::lean_dec(v___y_5385_);
    leanh::lean_dec_ref(v___y_5384_);
    return v_res_5387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(
    mut v_as_5388_: *mut leanh::LeanObject,
    mut v_i_5389_: usize,
    mut v_stop_5390_: usize,
    mut v_b_5391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: usize = 0;
    let mut v___x_5395_: usize = 0;
    let mut v___x_5397_: u8 = 0;
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5397_ = lean_usize_dec_eq(v_i_5389_, v_stop_5390_);
                if v___x_5397_ == 0 {
                    v___x_5398_ = lean_array_uget_borrowed(v_as_5388_, v_i_5389_);
                    leanh::lean_inc(v___x_5398_);
                    v___x_5399_ = l_Lean_Syntax_getKind(v___x_5398_);
                    v___x_5400_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__10;
                    v___x_5401_ = lean_name_eq(v___x_5399_, v___x_5400_);
                    leanh::lean_dec(v___x_5399_);
                    if v___x_5401_ == 0 {
                        v___y_5393_ = v_b_5391_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v___x_5398_);
                        v___x_5402_ = lean_array_push(v_b_5391_, v___x_5398_);
                        v___y_5393_ = v___x_5402_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5391_;
                }
            }
            1 => {
                v___x_5394_ = 1usize;
                v___x_5395_ = lean_usize_add(v_i_5389_, v___x_5394_);
                v_i_5389_ = v___x_5395_;
                v_b_5391_ = v___y_5393_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8___boxed(
    mut v_as_5403_: *mut leanh::LeanObject,
    mut v_i_5404_: *mut leanh::LeanObject,
    mut v_stop_5405_: *mut leanh::LeanObject,
    mut v_b_5406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5407_: usize = 0;
    let mut v_stop_boxed_5408_: usize = 0;
    let mut v_res_5409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5407_ = leanh::lean_unbox_usize(v_i_5404_);
    leanh::lean_dec(v_i_5404_);
    v_stop_boxed_5408_ = leanh::lean_unbox_usize(v_stop_5405_);
    leanh::lean_dec(v_stop_5405_);
    v_res_5409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v_as_5403_, v_i_boxed_5407_, v_stop_boxed_5408_, v_b_5406_);
    leanh::lean_dec_ref(v_as_5403_);
    return v_res_5409_;
}
pub unsafe fn l_Lean_Elab_Command_elabNotation(
    mut v_x_5452_: *mut leanh::LeanObject,
    mut v_a_5453_: *mut leanh::LeanObject,
    mut v_a_5454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v_val_5468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5474_: u8 = 0;
    let mut v_a_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5478_: u8 = 0;
    let mut v___x_5480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5482_: u8 = 0;
    let mut v___x_5483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5486_: u8 = 0;
    let mut v___y_5488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: u8 = 0;
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5546_: usize = 0;
    let mut v___y_5547_: u8 = 0;
    let mut v___y_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5555_: usize = 0;
    let mut v___x_5556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5565_: usize = 0;
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5574_: u8 = 0;
    let mut v___x_5576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5578_: u8 = 0;
    let mut v_a_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5582_: u8 = 0;
    let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5586_: u8 = 0;
    let mut v_a_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5590_: u8 = 0;
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v___x_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5607_: u8 = 0;
    let mut v___y_5608_: usize = 0;
    let mut v___y_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5634_: usize = 0;
    let mut v___x_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: u8 = 0;
    let mut v___x_5658_: u8 = 0;
    let mut v___x_5659_: usize = 0;
    let mut v___x_5660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: usize = 0;
    let mut v___x_5662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5666_: u8 = 0;
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5670_: u8 = 0;
    let mut v___y_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5682_: usize = 0;
    let mut v___y_5683_: u8 = 0;
    let mut v___y_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5717_: u8 = 0;
    let mut v___y_5718_: usize = 0;
    let mut v___y_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5748_: u8 = 0;
    let mut v___y_5749_: usize = 0;
    let mut v___y_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5781_: u8 = 0;
    let mut v___y_5782_: usize = 0;
    let mut v___y_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_items_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5813_: usize = 0;
    let mut v___x_5814_: usize = 0;
    let mut v___x_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: u8 = 0;
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5835_: u8 = 0;
    let mut v___x_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5839_: u8 = 0;
    let mut v_a_5840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5847_: u8 = 0;
    let mut v_a_5848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5851_: u8 = 0;
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_a_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5859_: u8 = 0;
    let mut v___x_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5863_: u8 = 0;
    let mut v___y_5865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: u8 = 0;
    let mut v___x_5878_: u8 = 0;
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: u8 = 0;
    let mut v___x_5883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: u8 = 0;
    let mut v___x_5900_: u8 = 0;
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: u8 = 0;
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrKind_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: u8 = 0;
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5924_: u8 = 0;
    let mut v___x_5925_: u8 = 0;
    let mut v___x_5926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5929_: u8 = 0;
    let mut v___x_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: u8 = 0;
    let mut v___x_5941_: u8 = 0;
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5945_: u8 = 0;
    let mut v___x_5946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: u8 = 0;
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: u8 = 0;
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5958_: u8 = 0;
    let mut v___x_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5483_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__0;
                v___x_5484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__1;
                v___x_5485_ = l_Lean_Elab_Command_elabNotation___closed__1;
                leanh::lean_inc(v_x_5452_);
                v___x_5486_ = l_Lean_Syntax_isOfKind(v_x_5452_, v___x_5485_);
                if v___x_5486_ == 0 {
                    leanh::lean_dec(v_x_5452_);
                    v___x_5595_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                    return v___x_5595_;
                } else {
                    v___x_5596_ = leanh::lean_unsigned_to_nat(0);
                    v___x_5951_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5596_);
                    v___x_5952_ = l_Lean_Syntax_isNone(v___x_5951_);
                    if v___x_5952_ == 0 {
                        v___x_5953_ = leanh::lean_unsigned_to_nat(1);
                        leanh::lean_inc(v___x_5951_);
                        v___x_5954_ = l_Lean_Syntax_matchesNull(v___x_5951_, v___x_5953_);
                        if v___x_5954_ == 0 {
                            leanh::lean_dec(v___x_5951_);
                            leanh::lean_dec(v_x_5452_);
                            v___x_5955_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                            return v___x_5955_;
                        } else {
                            v_doc_x3f_5956_ = l_Lean_Syntax_getArg(v___x_5951_, v___x_5596_);
                            leanh::lean_dec(v___x_5951_);
                            v___x_5957_ = l_Lean_Elab_Command_elabNotation___closed__15;
                            leanh::lean_inc(v_doc_x3f_5956_);
                            v___x_5958_ = l_Lean_Syntax_isOfKind(v_doc_x3f_5956_, v___x_5957_);
                            if v___x_5958_ == 0 {
                                leanh::lean_dec(v_doc_x3f_5956_);
                                leanh::lean_dec(v_x_5452_);
                                v___x_5959_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                                return v___x_5959_;
                            } else {
                                v___x_5960_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5960_, 0, v_doc_x3f_5956_);
                                v_doc_x3f_5935_ = v___x_5960_;
                                v___y_5936_ = v_a_5453_;
                                v___y_5937_ = v_a_5454_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_5951_);
                        v___x_5961_ = leanh::lean_box(0);
                        v_doc_x3f_5935_ = v___x_5961_;
                        v___y_5936_ = v_a_5453_;
                        v___y_5937_ = v_a_5454_;
                        state = 33;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5462_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_Command_mkUnexpander___boxed as *mut core::ffi::c_void,
                    5,
                    3,
                );
                leanh::lean_closure_set(v___x_5462_, 0, v___y_5459_);
                leanh::lean_closure_set(v___x_5462_, 1, v___y_5457_);
                leanh::lean_closure_set(v___x_5462_, 2, v___y_5458_);
                v___x_5463_ =
                    l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(
                        v___x_5462_,
                        v___y_5460_,
                        v___y_5461_,
                    );
                if leanh::lean_obj_tag(v___x_5463_) == 0 {
                    v_a_5464_ = leanh::lean_ctor_get(v___x_5463_, 0);
                    v_isSharedCheck_5474_ = (!leanh::lean_is_exclusive(v___x_5463_)) as u8;
                    if v_isSharedCheck_5474_ == 0 {
                        v___x_5466_ = v___x_5463_;
                        v_isShared_5467_ = v_isSharedCheck_5474_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5464_);
                        leanh::lean_dec(v___x_5463_);
                        v___x_5466_ = leanh::lean_box(0);
                        v_isShared_5467_ = v_isSharedCheck_5474_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_5475_ = leanh::lean_ctor_get(v___x_5463_, 0);
                    v_isSharedCheck_5482_ = (!leanh::lean_is_exclusive(v___x_5463_)) as u8;
                    if v_isSharedCheck_5482_ == 0 {
                        v___x_5477_ = v___x_5463_;
                        v_isShared_5478_ = v_isSharedCheck_5482_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5475_);
                        leanh::lean_dec(v___x_5463_);
                        v___x_5477_ = leanh::lean_box(0);
                        v_isShared_5478_ = v_isSharedCheck_5482_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5464_) == 1 {
                    leanh::lean_del_object(v___x_5466_);
                    v_val_5468_ = leanh::lean_ctor_get(v_a_5464_, 0);
                    leanh::lean_inc(v_val_5468_);
                    leanh::lean_dec_ref_known(v_a_5464_, 1);
                    v___x_5469_ =
                        l_Lean_Elab_Command_elabCommand(v_val_5468_, v___y_5460_, v___y_5461_);
                    return v___x_5469_;
                } else {
                    leanh::lean_dec(v_a_5464_);
                    v___x_5470_ = leanh::lean_box(0);
                    if v_isShared_5467_ == 0 {
                        leanh::lean_ctor_set(v___x_5466_, 0, v___x_5470_);
                        v___x_5472_ = v___x_5466_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5473_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5473_, 0, v___x_5470_);
                        v___x_5472_ = v_reuseFailAlloc_5473_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5472_;
            }
            4 => {
                if v_isShared_5478_ == 0 {
                    v___x_5480_ = v___x_5477_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5481_, 0, v_a_5475_);
                    v___x_5480_ = v_reuseFailAlloc_5481_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5480_;
            }
            6 => {
                v___x_5498_ = l_Lean_Elab_Command_elabNotation___closed__2;
                v___x_5499_ = l_Lean_Elab_Command_elabNotation___closed__3;
                leanh::lean_inc_ref(v___y_5494_);
                leanh::lean_inc_n(v___y_5497_, 4);
                leanh::lean_inc_n(v___y_5492_, 15);
                v___x_5500_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5500_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5500_, 1, v___y_5497_);
                leanh::lean_ctor_set(v___x_5500_, 2, v___y_5494_);
                v___x_5501_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5501_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5501_, 1, v___x_5498_);
                v___x_5502_ = l_Lean_Elab_Command_mkUnexpander___closed__29;
                leanh::lean_inc_ref_n(v___y_5491_, 4);
                v___x_5503_ =
                    l_Lean_Name_mkStr4(v___x_5483_, v___x_5484_, v___y_5491_, v___x_5502_);
                v___x_5504_ = l_Lean_Elab_Command_mkUnexpander___closed__31;
                v___x_5505_ =
                    l_Lean_Name_mkStr4(v___x_5483_, v___x_5484_, v___y_5491_, v___x_5504_);
                v___x_5506_ = l_Lean_Elab_Command_mkUnexpander___closed__33;
                v___x_5507_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5507_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5507_, 1, v___x_5506_);
                v___x_5508_ = l_Lean_Elab_Command_mkUnexpander___closed__34;
                v___x_5509_ =
                    l_Lean_Name_mkStr4(v___x_5483_, v___x_5484_, v___y_5491_, v___x_5508_);
                v___x_5510_ = l_Lean_Elab_Command_mkUnexpander___closed__36;
                v___x_5511_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5511_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5511_, 1, v___x_5510_);
                leanh::lean_inc_ref(v___y_5490_);
                v___x_5512_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5512_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5512_, 1, v___y_5490_);
                leanh::lean_inc_ref(v___x_5512_);
                leanh::lean_inc(v___y_5489_);
                leanh::lean_inc_ref(v___x_5511_);
                leanh::lean_inc(v___x_5509_);
                v___x_5513_ = l_Lean_Syntax_node3(
                    v___y_5492_,
                    v___x_5509_,
                    v___x_5511_,
                    v___y_5489_,
                    v___x_5512_,
                );
                v___x_5514_ = l_Lean_Syntax_node1(v___y_5492_, v___y_5497_, v___x_5513_);
                v___x_5515_ = l_Lean_Syntax_node1(v___y_5492_, v___y_5497_, v___x_5514_);
                v___x_5516_ = l_Lean_Elab_Command_mkUnexpander___closed__38;
                v___x_5517_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5517_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5517_, 1, v___x_5516_);
                v___x_5518_ = l_Lean_Elab_Command_elabNotation___closed__4;
                v___x_5519_ =
                    l_Lean_Name_mkStr4(v___x_5483_, v___x_5484_, v___y_5491_, v___x_5518_);
                v___x_5520_ = l_Lean_Elab_Command_elabNotation___closed__5;
                v___x_5521_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5521_, 0, v___y_5492_);
                leanh::lean_ctor_set(v___x_5521_, 1, v___x_5520_);
                leanh::lean_inc(v___y_5496_);
                v___x_5522_ = l_Lean_Syntax_node3(
                    v___y_5492_,
                    v___x_5509_,
                    v___x_5511_,
                    v___y_5496_,
                    v___x_5512_,
                );
                v___x_5523_ =
                    l_Lean_Syntax_node2(v___y_5492_, v___x_5519_, v___x_5521_, v___x_5522_);
                v___x_5524_ = l_Lean_Syntax_node4(
                    v___y_5492_,
                    v___x_5505_,
                    v___x_5507_,
                    v___x_5515_,
                    v___x_5517_,
                    v___x_5523_,
                );
                v___x_5525_ = l_Lean_Syntax_node1(v___y_5492_, v___y_5497_, v___x_5524_);
                v___x_5526_ = l_Lean_Syntax_node1(v___y_5492_, v___x_5503_, v___x_5525_);
                leanh::lean_inc_n(v___y_5495_, 2);
                leanh::lean_inc_ref_n(v___x_5500_, 2);
                v___x_5527_ = l_Lean_Syntax_node6(
                    v___y_5492_,
                    v___x_5499_,
                    v___x_5500_,
                    v___x_5500_,
                    v___y_5495_,
                    v___x_5501_,
                    v___x_5500_,
                    v___x_5526_,
                );
                v___x_5528_ = l_Lean_Elab_Command_isLocalAttrKind(v___y_5495_);
                if v___x_5528_ == 0 {
                    v___x_5529_ =
                        l_Lean_Elab_Command_elabCommand(v___x_5527_, v___y_5493_, v___y_5488_);
                    if leanh::lean_obj_tag(v___x_5529_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5529_, 1);
                        v___y_5457_ = v___y_5489_;
                        v___y_5458_ = v___y_5496_;
                        v___y_5459_ = v___y_5495_;
                        v___y_5460_ = v___y_5493_;
                        v___y_5461_ = v___y_5488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_5496_);
                        leanh::lean_dec(v___y_5495_);
                        leanh::lean_dec(v___y_5489_);
                        return v___x_5529_;
                    }
                } else {
                    v___x_5530_ = lean_st_ref_get(v___y_5488_);
                    v_scopes_5531_ = leanh::lean_ctor_get(v___x_5530_, 2);
                    leanh::lean_inc(v_scopes_5531_);
                    leanh::lean_dec(v___x_5530_);
                    v___x_5532_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_5533_ = l_List_head_x21___redArg(v___x_5532_, v_scopes_5531_);
                    leanh::lean_dec(v_scopes_5531_);
                    v_opts_5534_ = leanh::lean_ctor_get(v___x_5533_, 1);
                    leanh::lean_inc_ref(v_opts_5534_);
                    leanh::lean_dec(v___x_5533_);
                    v___x_5535_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
                    v___x_5536_ = l_Lean_Option_set___at___00Lean_Elab_Command_elabNotation_spec__6(
                        v_opts_5534_,
                        v___x_5535_,
                        v___x_5486_,
                    );
                    v___f_5537_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Command_elabNotation___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_5537_, 0, v___x_5536_);
                    v___x_5538_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Command_elabCommand___boxed as *mut core::ffi::c_void,
                        4,
                        1,
                    );
                    leanh::lean_closure_set(v___x_5538_, 0, v___x_5527_);
                    v___x_5539_ = l_Lean_Elab_Command_withScope___redArg(
                        v___f_5537_,
                        v___x_5538_,
                        v___y_5493_,
                        v___y_5488_,
                    );
                    if leanh::lean_obj_tag(v___x_5539_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5539_, 1);
                        v___y_5457_ = v___y_5489_;
                        v___y_5458_ = v___y_5496_;
                        v___y_5459_ = v___y_5495_;
                        v___y_5460_ = v___y_5493_;
                        v___y_5461_ = v___y_5488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_5496_);
                        leanh::lean_dec(v___y_5495_);
                        leanh::lean_dec(v___y_5489_);
                        return v___x_5539_;
                    }
                }
            }
            7 => {
                v_sz_5555_ = lean_array_size(v___y_5548_);
                v___x_5556_ = leanh::lean_box_usize(v_sz_5555_);
                v___x_5557_ = leanh::lean_box_usize(v___y_5546_);
                v___x_5558_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__4___boxed as *mut core::ffi::c_void, 5, 3);
                leanh::lean_closure_set(v___x_5558_, 0, v___x_5556_);
                leanh::lean_closure_set(v___x_5558_, 1, v___x_5557_);
                leanh::lean_closure_set(v___x_5558_, 2, v___y_5548_);
                v___x_5559_ =
                    l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(
                        v___x_5558_,
                        v___y_5545_,
                        v___y_5541_,
                    );
                if leanh::lean_obj_tag(v___x_5559_) == 0 {
                    v_a_5560_ = leanh::lean_ctor_get(v___x_5559_, 0);
                    leanh::lean_inc(v_a_5560_);
                    leanh::lean_dec_ref_known(v___x_5559_, 1);
                    v___x_5561_ = l_Lean_Elab_Command_getRef___redArg(v___y_5545_);
                    if leanh::lean_obj_tag(v___x_5561_) == 0 {
                        v_a_5562_ = leanh::lean_ctor_get(v___x_5561_, 0);
                        leanh::lean_inc(v_a_5562_);
                        leanh::lean_dec_ref_known(v___x_5561_, 1);
                        v___x_5563_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5545_);
                        if leanh::lean_obj_tag(v___x_5563_) == 0 {
                            leanh::lean_dec_ref_known(v___x_5563_, 1);
                            v_quotContext_x3f_5564_ = leanh::lean_ctor_get(v___y_5545_, 5);
                            v_sz_5565_ = lean_array_size(v___y_5554_);
                            v___x_5566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__5(v_sz_5565_, v___y_5546_, v___y_5554_);
                            v___x_5567_ =
                                l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote(
                                    v___x_5566_,
                                    v___y_5553_,
                                );
                            leanh::lean_dec_ref(v___x_5566_);
                            v___x_5568_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            leanh::lean_ctor_set(v___x_5568_, 0, v___y_5543_);
                            leanh::lean_ctor_set(v___x_5568_, 1, v___y_5542_);
                            leanh::lean_ctor_set(v___x_5568_, 2, v_a_5560_);
                            v___x_5569_ = l_Lean_SourceInfo_fromRef(v_a_5562_, v___y_5547_);
                            leanh::lean_dec(v_a_5562_);
                            if leanh::lean_obj_tag(v_quotContext_x3f_5564_) == 0 {
                                v___x_5570_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_5541_);
                                leanh::lean_dec_ref(v___x_5570_);
                                v___y_5488_ = v___y_5541_;
                                v___y_5489_ = v___x_5568_;
                                v___y_5490_ = v___y_5544_;
                                v___y_5491_ = v___y_5549_;
                                v___y_5492_ = v___x_5569_;
                                v___y_5493_ = v___y_5545_;
                                v___y_5494_ = v___y_5550_;
                                v___y_5495_ = v___y_5551_;
                                v___y_5496_ = v___x_5567_;
                                v___y_5497_ = v___y_5552_;
                                state = 6;
                                continue;
                            } else {
                                v___y_5488_ = v___y_5541_;
                                v___y_5489_ = v___x_5568_;
                                v___y_5490_ = v___y_5544_;
                                v___y_5491_ = v___y_5549_;
                                v___y_5492_ = v___x_5569_;
                                v___y_5493_ = v___y_5545_;
                                v___y_5494_ = v___y_5550_;
                                v___y_5495_ = v___y_5551_;
                                v___y_5496_ = v___x_5567_;
                                v___y_5497_ = v___y_5552_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_5562_);
                            leanh::lean_dec(v_a_5560_);
                            leanh::lean_dec_ref(v___y_5554_);
                            leanh::lean_dec(v___y_5553_);
                            leanh::lean_dec(v___y_5551_);
                            leanh::lean_dec(v___y_5543_);
                            leanh::lean_dec(v___y_5542_);
                            v_a_5571_ = leanh::lean_ctor_get(v___x_5563_, 0);
                            v_isSharedCheck_5578_ =
                                (!leanh::lean_is_exclusive(v___x_5563_)) as u8;
                            if v_isSharedCheck_5578_ == 0 {
                                v___x_5573_ = v___x_5563_;
                                v_isShared_5574_ = v_isSharedCheck_5578_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5571_);
                                leanh::lean_dec(v___x_5563_);
                                v___x_5573_ = leanh::lean_box(0);
                                v_isShared_5574_ = v_isSharedCheck_5578_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_5560_);
                        leanh::lean_dec_ref(v___y_5554_);
                        leanh::lean_dec(v___y_5553_);
                        leanh::lean_dec(v___y_5551_);
                        leanh::lean_dec(v___y_5543_);
                        leanh::lean_dec(v___y_5542_);
                        v_a_5579_ = leanh::lean_ctor_get(v___x_5561_, 0);
                        v_isSharedCheck_5586_ =
                            (!leanh::lean_is_exclusive(v___x_5561_)) as u8;
                        if v_isSharedCheck_5586_ == 0 {
                            v___x_5581_ = v___x_5561_;
                            v_isShared_5582_ = v_isSharedCheck_5586_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5579_);
                            leanh::lean_dec(v___x_5561_);
                            v___x_5581_ = leanh::lean_box(0);
                            v_isShared_5582_ = v_isSharedCheck_5586_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___y_5554_);
                    leanh::lean_dec(v___y_5553_);
                    leanh::lean_dec(v___y_5551_);
                    leanh::lean_dec(v___y_5543_);
                    leanh::lean_dec(v___y_5542_);
                    v_a_5587_ = leanh::lean_ctor_get(v___x_5559_, 0);
                    v_isSharedCheck_5594_ = (!leanh::lean_is_exclusive(v___x_5559_)) as u8;
                    if v_isSharedCheck_5594_ == 0 {
                        v___x_5589_ = v___x_5559_;
                        v_isShared_5590_ = v_isSharedCheck_5594_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5587_);
                        leanh::lean_dec(v___x_5559_);
                        v___x_5589_ = leanh::lean_box(0);
                        v_isShared_5590_ = v_isSharedCheck_5594_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_5574_ == 0 {
                    v___x_5576_ = v___x_5573_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_a_5571_);
                    v___x_5576_ = v_reuseFailAlloc_5577_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5576_;
            }
            10 => {
                if v_isShared_5582_ == 0 {
                    v___x_5584_ = v___x_5581_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v_a_5579_);
                    v___x_5584_ = v_reuseFailAlloc_5585_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5584_;
            }
            12 => {
                if v_isShared_5590_ == 0 {
                    v___x_5592_ = v___x_5589_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 0, v_a_5587_);
                    v___x_5592_ = v_reuseFailAlloc_5593_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5592_;
            }
            14 => {
                leanh::lean_inc_ref_n(v___y_5613_, 2);
                v___x_5618_ = l_Array_append___redArg(v___y_5613_, v___y_5617_);
                leanh::lean_dec_ref(v___y_5617_);
                leanh::lean_inc_n(v___y_5616_, 3);
                leanh::lean_inc_n(v___y_5603_, 9);
                v___x_5619_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5619_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5619_, 1, v___y_5616_);
                leanh::lean_ctor_set(v___x_5619_, 2, v___x_5618_);
                v___x_5620_ = l_Lean_Elab_Command_elabNotation___closed__7;
                v___x_5621_ = l_Lean_Elab_Command_mkUnexpander___closed__53;
                v___x_5622_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5622_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5622_, 1, v___x_5621_);
                v___x_5623_ = l_Lean_Elab_Command_elabNotation___closed__8;
                v___x_5624_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5624_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5624_, 1, v___x_5623_);
                v___x_5625_ = l_Lean_Elab_Command_mkUnexpander___closed__26;
                v___x_5626_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5626_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5626_, 1, v___x_5625_);
                v___x_5627_ = l_Nat_reprFast(v___y_5609_);
                v___x_5628_ = leanh::lean_box(2);
                v___x_5629_ = l_Lean_Syntax_mkNumLit(v___x_5627_, v___x_5628_);
                v___x_5630_ = l_Lean_Elab_Command_mkUnexpander___closed__37;
                v___x_5631_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5631_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5631_, 1, v___x_5630_);
                v___x_5632_ = l_Lean_Syntax_node5(
                    v___y_5603_,
                    v___x_5620_,
                    v___x_5622_,
                    v___x_5624_,
                    v___x_5626_,
                    v___x_5629_,
                    v___x_5631_,
                );
                v___x_5633_ = l_Lean_Syntax_node1(v___y_5603_, v___y_5616_, v___x_5632_);
                v_sz_5634_ = lean_array_size(v___y_5602_);
                v___x_5635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__3(v_sz_5634_, v___y_5608_, v___y_5602_);
                v___x_5636_ = l_Array_append___redArg(v___y_5613_, v___x_5635_);
                leanh::lean_dec_ref(v___x_5635_);
                v___x_5637_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5637_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5637_, 1, v___y_5616_);
                leanh::lean_ctor_set(v___x_5637_, 2, v___x_5636_);
                v___x_5638_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
                v___x_5639_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5639_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5639_, 1, v___x_5638_);
                v___x_5640_ = leanh::lean_unsigned_to_nat(10);
                v___x_5641_ = lean_mk_empty_array_with_capacity(v___x_5640_);
                v___x_5642_ = lean_array_push(v___x_5641_, v___y_5598_);
                v___x_5643_ = lean_array_push(v___x_5642_, v___y_5606_);
                leanh::lean_inc(v___y_5614_);
                v___x_5644_ = lean_array_push(v___x_5643_, v___y_5614_);
                v___x_5645_ = lean_array_push(v___x_5644_, v___y_5599_);
                v___x_5646_ = lean_array_push(v___x_5645_, v___y_5612_);
                v___x_5647_ = lean_array_push(v___x_5646_, v___x_5619_);
                v___x_5648_ = lean_array_push(v___x_5647_, v___x_5633_);
                v___x_5649_ = lean_array_push(v___x_5648_, v___x_5637_);
                v___x_5650_ = lean_array_push(v___x_5649_, v___x_5639_);
                v___x_5651_ = lean_array_push(v___x_5650_, v___y_5600_);
                leanh::lean_inc(v___y_5604_);
                v___x_5652_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5652_, 0, v___y_5603_);
                leanh::lean_ctor_set(v___x_5652_, 1, v___y_5604_);
                leanh::lean_ctor_set(v___x_5652_, 2, v___x_5651_);
                v___x_5653_ = l_Lean_Elab_Command_elabSyntax(v___x_5652_, v___y_5605_, v___y_5601_);
                if leanh::lean_obj_tag(v___x_5653_) == 0 {
                    v_a_5654_ = leanh::lean_ctor_get(v___x_5653_, 0);
                    leanh::lean_inc(v_a_5654_);
                    leanh::lean_dec_ref_known(v___x_5653_, 1);
                    v___x_5655_ = lean_array_get_size(v___y_5610_);
                    v___x_5656_ = l_Lean_Elab_Command_mkUnexpander___closed__68;
                    v___x_5657_ = lean_nat_dec_lt(v___x_5596_, v___x_5655_);
                    if v___x_5657_ == 0 {
                        v___y_5541_ = v___y_5601_;
                        v___y_5542_ = v_a_5654_;
                        v___y_5543_ = v___x_5628_;
                        v___y_5544_ = v___x_5630_;
                        v___y_5545_ = v___y_5605_;
                        v___y_5546_ = v___y_5608_;
                        v___y_5547_ = v___y_5607_;
                        v___y_5548_ = v___y_5610_;
                        v___y_5549_ = v___y_5611_;
                        v___y_5550_ = v___y_5613_;
                        v___y_5551_ = v___y_5614_;
                        v___y_5552_ = v___y_5616_;
                        v___y_5553_ = v___y_5615_;
                        v___y_5554_ = v___x_5656_;
                        state = 7;
                        continue;
                    } else {
                        v___x_5658_ = lean_nat_dec_le(v___x_5655_, v___x_5655_);
                        if v___x_5658_ == 0 {
                            if v___x_5657_ == 0 {
                                v___y_5541_ = v___y_5601_;
                                v___y_5542_ = v_a_5654_;
                                v___y_5543_ = v___x_5628_;
                                v___y_5544_ = v___x_5630_;
                                v___y_5545_ = v___y_5605_;
                                v___y_5546_ = v___y_5608_;
                                v___y_5547_ = v___y_5607_;
                                v___y_5548_ = v___y_5610_;
                                v___y_5549_ = v___y_5611_;
                                v___y_5550_ = v___y_5613_;
                                v___y_5551_ = v___y_5614_;
                                v___y_5552_ = v___y_5616_;
                                v___y_5553_ = v___y_5615_;
                                v___y_5554_ = v___x_5656_;
                                state = 7;
                                continue;
                            } else {
                                v___x_5659_ = lean_usize_of_nat(v___x_5655_);
                                v___x_5660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_5610_, v___y_5608_, v___x_5659_, v___x_5656_);
                                v___y_5541_ = v___y_5601_;
                                v___y_5542_ = v_a_5654_;
                                v___y_5543_ = v___x_5628_;
                                v___y_5544_ = v___x_5630_;
                                v___y_5545_ = v___y_5605_;
                                v___y_5546_ = v___y_5608_;
                                v___y_5547_ = v___y_5607_;
                                v___y_5548_ = v___y_5610_;
                                v___y_5549_ = v___y_5611_;
                                v___y_5550_ = v___y_5613_;
                                v___y_5551_ = v___y_5614_;
                                v___y_5552_ = v___y_5616_;
                                v___y_5553_ = v___y_5615_;
                                v___y_5554_ = v___x_5660_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v___x_5661_ = lean_usize_of_nat(v___x_5655_);
                            v___x_5662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Command_elabNotation_spec__8(v___y_5610_, v___y_5608_, v___x_5661_, v___x_5656_);
                            v___y_5541_ = v___y_5601_;
                            v___y_5542_ = v_a_5654_;
                            v___y_5543_ = v___x_5628_;
                            v___y_5544_ = v___x_5630_;
                            v___y_5545_ = v___y_5605_;
                            v___y_5546_ = v___y_5608_;
                            v___y_5547_ = v___y_5607_;
                            v___y_5548_ = v___y_5610_;
                            v___y_5549_ = v___y_5611_;
                            v___y_5550_ = v___y_5613_;
                            v___y_5551_ = v___y_5614_;
                            v___y_5552_ = v___y_5616_;
                            v___y_5553_ = v___y_5615_;
                            v___y_5554_ = v___x_5662_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_5615_);
                    leanh::lean_dec(v___y_5614_);
                    leanh::lean_dec_ref(v___y_5610_);
                    v_a_5663_ = leanh::lean_ctor_get(v___x_5653_, 0);
                    v_isSharedCheck_5670_ = (!leanh::lean_is_exclusive(v___x_5653_)) as u8;
                    if v_isSharedCheck_5670_ == 0 {
                        v___x_5665_ = v___x_5653_;
                        v_isShared_5666_ = v_isSharedCheck_5670_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5663_);
                        leanh::lean_dec(v___x_5653_);
                        v___x_5665_ = leanh::lean_box(0);
                        v_isShared_5666_ = v_isSharedCheck_5670_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5666_ == 0 {
                    v___x_5668_ = v___x_5665_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_a_5663_);
                    v___x_5668_ = v_reuseFailAlloc_5669_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5668_;
            }
            17 => {
                leanh::lean_inc_ref(v___y_5687_);
                v___x_5692_ = l_Array_append___redArg(v___y_5687_, v___y_5691_);
                leanh::lean_dec_ref(v___y_5691_);
                leanh::lean_inc(v___y_5690_);
                leanh::lean_inc(v___y_5677_);
                v___x_5693_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5693_, 0, v___y_5677_);
                leanh::lean_ctor_set(v___x_5693_, 1, v___y_5690_);
                leanh::lean_ctor_set(v___x_5693_, 2, v___x_5692_);
                if leanh::lean_obj_tag(v___y_5680_) == 1 {
                    v_val_5694_ = leanh::lean_ctor_get(v___y_5680_, 0);
                    leanh::lean_inc(v_val_5694_);
                    leanh::lean_dec_ref_known(v___y_5680_, 1);
                    v___x_5695_ = l_Lean_Elab_Command_elabNotation___closed__10;
                    v___x_5696_ = l_Lean_Elab_Command_mkUnexpander___closed__53;
                    leanh::lean_inc_n(v___y_5677_, 5);
                    v___x_5697_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5697_, 0, v___y_5677_);
                    leanh::lean_ctor_set(v___x_5697_, 1, v___x_5696_);
                    v___x_5698_ = l_Lean_Elab_Command_elabNotation___closed__11;
                    v___x_5699_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5699_, 0, v___y_5677_);
                    leanh::lean_ctor_set(v___x_5699_, 1, v___x_5698_);
                    v___x_5700_ = l_Lean_Elab_Command_mkUnexpander___closed__26;
                    v___x_5701_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5701_, 0, v___y_5677_);
                    leanh::lean_ctor_set(v___x_5701_, 1, v___x_5700_);
                    v___x_5702_ = l_Lean_Elab_Command_mkUnexpander___closed__37;
                    v___x_5703_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5703_, 0, v___y_5677_);
                    leanh::lean_ctor_set(v___x_5703_, 1, v___x_5702_);
                    v___x_5704_ = l_Lean_Syntax_node5(
                        v___y_5677_,
                        v___x_5695_,
                        v___x_5697_,
                        v___x_5699_,
                        v___x_5701_,
                        v_val_5694_,
                        v___x_5703_,
                    );
                    v___x_5705_ = l_Array_mkArray1___redArg(v___x_5704_);
                    v___y_5598_ = v___y_5672_;
                    v___y_5599_ = v___y_5673_;
                    v___y_5600_ = v___y_5674_;
                    v___y_5601_ = v___y_5675_;
                    v___y_5602_ = v___y_5676_;
                    v___y_5603_ = v___y_5677_;
                    v___y_5604_ = v___y_5678_;
                    v___y_5605_ = v___y_5679_;
                    v___y_5606_ = v___y_5681_;
                    v___y_5607_ = v___y_5683_;
                    v___y_5608_ = v___y_5682_;
                    v___y_5609_ = v___y_5684_;
                    v___y_5610_ = v___y_5685_;
                    v___y_5611_ = v___y_5686_;
                    v___y_5612_ = v___x_5693_;
                    v___y_5613_ = v___y_5687_;
                    v___y_5614_ = v___y_5688_;
                    v___y_5615_ = v___y_5689_;
                    v___y_5616_ = v___y_5690_;
                    v___y_5617_ = v___x_5705_;
                    state = 14;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5680_);
                    v___x_5706_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
                    v___y_5598_ = v___y_5672_;
                    v___y_5599_ = v___y_5673_;
                    v___y_5600_ = v___y_5674_;
                    v___y_5601_ = v___y_5675_;
                    v___y_5602_ = v___y_5676_;
                    v___y_5603_ = v___y_5677_;
                    v___y_5604_ = v___y_5678_;
                    v___y_5605_ = v___y_5679_;
                    v___y_5606_ = v___y_5681_;
                    v___y_5607_ = v___y_5683_;
                    v___y_5608_ = v___y_5682_;
                    v___y_5609_ = v___y_5684_;
                    v___y_5610_ = v___y_5685_;
                    v___y_5611_ = v___y_5686_;
                    v___y_5612_ = v___x_5693_;
                    v___y_5613_ = v___y_5687_;
                    v___y_5614_ = v___y_5688_;
                    v___y_5615_ = v___y_5689_;
                    v___y_5616_ = v___y_5690_;
                    v___y_5617_ = v___x_5706_;
                    state = 14;
                    continue;
                }
            }
            18 => {
                leanh::lean_inc_ref(v___y_5723_);
                v___x_5728_ = l_Array_append___redArg(v___y_5723_, v___y_5727_);
                leanh::lean_dec_ref(v___y_5727_);
                leanh::lean_inc(v___y_5726_);
                leanh::lean_inc_n(v___y_5712_, 2);
                v___x_5729_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5729_, 0, v___y_5712_);
                leanh::lean_ctor_set(v___x_5729_, 1, v___y_5726_);
                leanh::lean_ctor_set(v___x_5729_, 2, v___x_5728_);
                leanh::lean_inc_ref(v___y_5714_);
                v___x_5730_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5730_, 0, v___y_5712_);
                leanh::lean_ctor_set(v___x_5730_, 1, v___y_5714_);
                if leanh::lean_obj_tag(v___y_5722_) == 1 {
                    v_val_5731_ = leanh::lean_ctor_get(v___y_5722_, 0);
                    leanh::lean_inc(v_val_5731_);
                    leanh::lean_dec_ref_known(v___y_5722_, 1);
                    v___x_5732_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
                    v___x_5733_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__6;
                    leanh::lean_inc_n(v___y_5712_, 2);
                    v___x_5734_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5734_, 0, v___y_5712_);
                    leanh::lean_ctor_set(v___x_5734_, 1, v___x_5733_);
                    v___x_5735_ =
                        l_Lean_Syntax_node2(v___y_5712_, v___x_5732_, v___x_5734_, v_val_5731_);
                    v___x_5736_ = l_Array_mkArray1___redArg(v___x_5735_);
                    v___y_5672_ = v___y_5708_;
                    v___y_5673_ = v___x_5730_;
                    v___y_5674_ = v___y_5709_;
                    v___y_5675_ = v___y_5710_;
                    v___y_5676_ = v___y_5711_;
                    v___y_5677_ = v___y_5712_;
                    v___y_5678_ = v___y_5713_;
                    v___y_5679_ = v___y_5715_;
                    v___y_5680_ = v___y_5716_;
                    v___y_5681_ = v___x_5729_;
                    v___y_5682_ = v___y_5718_;
                    v___y_5683_ = v___y_5717_;
                    v___y_5684_ = v___y_5719_;
                    v___y_5685_ = v___y_5720_;
                    v___y_5686_ = v___y_5721_;
                    v___y_5687_ = v___y_5723_;
                    v___y_5688_ = v___y_5724_;
                    v___y_5689_ = v___y_5725_;
                    v___y_5690_ = v___y_5726_;
                    v___y_5691_ = v___x_5736_;
                    state = 17;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5722_);
                    v___x_5737_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
                    v___y_5672_ = v___y_5708_;
                    v___y_5673_ = v___x_5730_;
                    v___y_5674_ = v___y_5709_;
                    v___y_5675_ = v___y_5710_;
                    v___y_5676_ = v___y_5711_;
                    v___y_5677_ = v___y_5712_;
                    v___y_5678_ = v___y_5713_;
                    v___y_5679_ = v___y_5715_;
                    v___y_5680_ = v___y_5716_;
                    v___y_5681_ = v___x_5729_;
                    v___y_5682_ = v___y_5718_;
                    v___y_5683_ = v___y_5717_;
                    v___y_5684_ = v___y_5719_;
                    v___y_5685_ = v___y_5720_;
                    v___y_5686_ = v___y_5721_;
                    v___y_5687_ = v___y_5723_;
                    v___y_5688_ = v___y_5724_;
                    v___y_5689_ = v___y_5725_;
                    v___y_5690_ = v___y_5726_;
                    v___y_5691_ = v___x_5737_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                leanh::lean_inc_ref(v___y_5754_);
                v___x_5759_ = l_Array_append___redArg(v___y_5754_, v___y_5758_);
                leanh::lean_dec_ref(v___y_5758_);
                leanh::lean_inc(v___y_5757_);
                leanh::lean_inc(v___y_5743_);
                v___x_5760_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5760_, 0, v___y_5743_);
                leanh::lean_ctor_set(v___x_5760_, 1, v___y_5757_);
                leanh::lean_ctor_set(v___x_5760_, 2, v___x_5759_);
                if leanh::lean_obj_tag(v___y_5740_) == 1 {
                    v_val_5761_ = leanh::lean_ctor_get(v___y_5740_, 0);
                    leanh::lean_inc(v_val_5761_);
                    leanh::lean_dec_ref_known(v___y_5740_, 1);
                    v___x_5762_ = l_Lean_Elab_Command_mkUnexpander___closed__11;
                    leanh::lean_inc_ref(v___y_5752_);
                    v___x_5763_ =
                        l_Lean_Name_mkStr4(v___x_5483_, v___x_5484_, v___y_5752_, v___x_5762_);
                    v___x_5764_ = l_Lean_Elab_Command_mkUnexpander___closed__13;
                    leanh::lean_inc_n(v___y_5743_, 4);
                    v___x_5765_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5765_, 0, v___y_5743_);
                    leanh::lean_ctor_set(v___x_5765_, 1, v___x_5764_);
                    leanh::lean_inc_ref(v___y_5754_);
                    v___x_5766_ = l_Array_append___redArg(v___y_5754_, v_val_5761_);
                    leanh::lean_dec(v_val_5761_);
                    leanh::lean_inc(v___y_5757_);
                    v___x_5767_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5767_, 0, v___y_5743_);
                    leanh::lean_ctor_set(v___x_5767_, 1, v___y_5757_);
                    leanh::lean_ctor_set(v___x_5767_, 2, v___x_5766_);
                    v___x_5768_ = l_Lean_Elab_Command_mkUnexpander___closed__17;
                    v___x_5769_ = leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5769_, 0, v___y_5743_);
                    leanh::lean_ctor_set(v___x_5769_, 1, v___x_5768_);
                    v___x_5770_ = l_Lean_Syntax_node3(
                        v___y_5743_,
                        v___x_5763_,
                        v___x_5765_,
                        v___x_5767_,
                        v___x_5769_,
                    );
                    v___x_5771_ = l_Array_mkArray1___redArg(v___x_5770_);
                    v___y_5708_ = v___x_5760_;
                    v___y_5709_ = v___y_5739_;
                    v___y_5710_ = v___y_5741_;
                    v___y_5711_ = v___y_5742_;
                    v___y_5712_ = v___y_5743_;
                    v___y_5713_ = v___y_5744_;
                    v___y_5714_ = v___y_5745_;
                    v___y_5715_ = v___y_5746_;
                    v___y_5716_ = v___y_5747_;
                    v___y_5717_ = v___y_5748_;
                    v___y_5718_ = v___y_5749_;
                    v___y_5719_ = v___y_5750_;
                    v___y_5720_ = v___y_5751_;
                    v___y_5721_ = v___y_5752_;
                    v___y_5722_ = v___y_5753_;
                    v___y_5723_ = v___y_5754_;
                    v___y_5724_ = v___y_5755_;
                    v___y_5725_ = v___y_5756_;
                    v___y_5726_ = v___y_5757_;
                    v___y_5727_ = v___x_5771_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5740_);
                    v___x_5772_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
                    v___y_5708_ = v___x_5760_;
                    v___y_5709_ = v___y_5739_;
                    v___y_5710_ = v___y_5741_;
                    v___y_5711_ = v___y_5742_;
                    v___y_5712_ = v___y_5743_;
                    v___y_5713_ = v___y_5744_;
                    v___y_5714_ = v___y_5745_;
                    v___y_5715_ = v___y_5746_;
                    v___y_5716_ = v___y_5747_;
                    v___y_5717_ = v___y_5748_;
                    v___y_5718_ = v___y_5749_;
                    v___y_5719_ = v___y_5750_;
                    v___y_5720_ = v___y_5751_;
                    v___y_5721_ = v___y_5752_;
                    v___y_5722_ = v___y_5753_;
                    v___y_5723_ = v___y_5754_;
                    v___y_5724_ = v___y_5755_;
                    v___y_5725_ = v___y_5756_;
                    v___y_5726_ = v___y_5757_;
                    v___y_5727_ = v___x_5772_;
                    state = 18;
                    continue;
                }
            }
            20 => {
                v___x_5790_ = l_Lean_Elab_Command_elabNotation___closed__12;
                v___x_5791_ = l_Lean_Elab_Command_elabNotation___closed__13;
                v___x_5792_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__13;
                v___x_5793_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__14);
                if leanh::lean_obj_tag(v___y_5784_) == 1 {
                    v_val_5794_ = leanh::lean_ctor_get(v___y_5784_, 0);
                    leanh::lean_inc(v_val_5794_);
                    leanh::lean_dec_ref_known(v___y_5784_, 1);
                    v___x_5795_ = l_Array_mkArray1___redArg(v_val_5794_);
                    v___y_5739_ = v___y_5774_;
                    v___y_5740_ = v___y_5775_;
                    v___y_5741_ = v___y_5776_;
                    v___y_5742_ = v___y_5777_;
                    v___y_5743_ = v___y_5778_;
                    v___y_5744_ = v___x_5791_;
                    v___y_5745_ = v___x_5790_;
                    v___y_5746_ = v___y_5779_;
                    v___y_5747_ = v___y_5780_;
                    v___y_5748_ = v___y_5781_;
                    v___y_5749_ = v___y_5782_;
                    v___y_5750_ = v___y_5783_;
                    v___y_5751_ = v___y_5785_;
                    v___y_5752_ = v___y_5786_;
                    v___y_5753_ = v___y_5787_;
                    v___y_5754_ = v___x_5793_;
                    v___y_5755_ = v___y_5788_;
                    v___y_5756_ = v___y_5789_;
                    v___y_5757_ = v___x_5792_;
                    v___y_5758_ = v___x_5795_;
                    state = 19;
                    continue;
                } else {
                    leanh::lean_dec(v___y_5784_);
                    v___x_5796_ = l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__7;
                    v___y_5739_ = v___y_5774_;
                    v___y_5740_ = v___y_5775_;
                    v___y_5741_ = v___y_5776_;
                    v___y_5742_ = v___y_5777_;
                    v___y_5743_ = v___y_5778_;
                    v___y_5744_ = v___x_5791_;
                    v___y_5745_ = v___x_5790_;
                    v___y_5746_ = v___y_5779_;
                    v___y_5747_ = v___y_5780_;
                    v___y_5748_ = v___y_5781_;
                    v___y_5749_ = v___y_5782_;
                    v___y_5750_ = v___y_5783_;
                    v___y_5751_ = v___y_5785_;
                    v___y_5752_ = v___y_5786_;
                    v___y_5753_ = v___y_5787_;
                    v___y_5754_ = v___x_5793_;
                    v___y_5755_ = v___y_5788_;
                    v___y_5756_ = v___y_5789_;
                    v___y_5757_ = v___x_5792_;
                    v___y_5758_ = v___x_5796_;
                    state = 19;
                    continue;
                }
            }
            21 => {
                v___x_5807_ = leanh::lean_alloc_closure(
                    l_Lean_evalOptPrio___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                leanh::lean_closure_set(v___x_5807_, 0, v_prio_x3f_5804_);
                v___x_5808_ =
                    l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(
                        v___x_5807_,
                        v___y_5805_,
                        v___y_5806_,
                    );
                if leanh::lean_obj_tag(v___x_5808_) == 0 {
                    v_a_5809_ = leanh::lean_ctor_get(v___x_5808_, 0);
                    leanh::lean_inc(v_a_5809_);
                    leanh::lean_dec_ref_known(v___x_5808_, 1);
                    v___x_5810_ = leanh::lean_unsigned_to_nat(7);
                    v___x_5811_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5810_);
                    v_items_5812_ = l_Lean_Syntax_getArgs(v___x_5811_);
                    leanh::lean_dec(v___x_5811_);
                    v_sz_5813_ = lean_array_size(v_items_5812_);
                    v___x_5814_ = 0usize;
                    v___x_5815_ = leanh::lean_box_usize(v_sz_5813_);
                    v___x_5816_ = l_Lean_Elab_Command_elabNotation___boxed__const__1;
                    leanh::lean_inc_ref(v_items_5812_);
                    v___x_5817_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabNotation_spec__2___boxed as *mut core::ffi::c_void, 5, 3);
                    leanh::lean_closure_set(v___x_5817_, 0, v___x_5815_);
                    leanh::lean_closure_set(v___x_5817_, 1, v___x_5816_);
                    leanh::lean_closure_set(v___x_5817_, 2, v_items_5812_);
                    v___x_5818_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(v___x_5817_, v___y_5805_, v___y_5806_);
                    if leanh::lean_obj_tag(v___x_5818_) == 0 {
                        v_a_5819_ = leanh::lean_ctor_get(v___x_5818_, 0);
                        leanh::lean_inc(v_a_5819_);
                        leanh::lean_dec_ref_known(v___x_5818_, 1);
                        v___x_5820_ = l_Lean_Elab_Command_getRef___redArg(v___y_5805_);
                        if leanh::lean_obj_tag(v___x_5820_) == 0 {
                            v_a_5821_ = leanh::lean_ctor_get(v___x_5820_, 0);
                            leanh::lean_inc(v_a_5821_);
                            leanh::lean_dec_ref_known(v___x_5820_, 1);
                            v___x_5822_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5805_);
                            if leanh::lean_obj_tag(v___x_5822_) == 0 {
                                leanh::lean_dec_ref_known(v___x_5822_, 1);
                                v_quotContext_x3f_5823_ =
                                    leanh::lean_ctor_get(v___y_5805_, 5);
                                v___x_5824_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_antiquote___closed__3;
                                v___x_5825_ = 0;
                                v___x_5826_ =
                                    l_Lean_mkIdentFrom(v_x_5452_, v___x_5824_, v___x_5825_);
                                v___x_5827_ = leanh::lean_unsigned_to_nat(9);
                                v_rhs_5828_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5827_);
                                leanh::lean_dec(v_x_5452_);
                                leanh::lean_inc(v_rhs_5828_);
                                v_attrs_x3f_5829_ = l_Lean_Elab_Command_addInheritDocDefault(
                                    v_rhs_5828_,
                                    v___y_5798_,
                                );
                                v___x_5830_ = l_Lean_SourceInfo_fromRef(v_a_5821_, v___x_5825_);
                                leanh::lean_dec(v_a_5821_);
                                if leanh::lean_obj_tag(v_quotContext_x3f_5823_) == 0 {
                                    v___x_5831_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabNotation_spec__7___redArg(v___y_5806_);
                                    leanh::lean_dec_ref(v___x_5831_);
                                    v___y_5774_ = v___x_5826_;
                                    v___y_5775_ = v_attrs_x3f_5829_;
                                    v___y_5776_ = v___y_5806_;
                                    v___y_5777_ = v_a_5819_;
                                    v___y_5778_ = v___x_5830_;
                                    v___y_5779_ = v___y_5805_;
                                    v___y_5780_ = v___y_5802_;
                                    v___y_5781_ = v___x_5825_;
                                    v___y_5782_ = v___x_5814_;
                                    v___y_5783_ = v_a_5809_;
                                    v___y_5784_ = v___y_5799_;
                                    v___y_5785_ = v_items_5812_;
                                    v___y_5786_ = v___y_5800_;
                                    v___y_5787_ = v___y_5801_;
                                    v___y_5788_ = v___y_5803_;
                                    v___y_5789_ = v_rhs_5828_;
                                    state = 20;
                                    continue;
                                } else {
                                    v___y_5774_ = v___x_5826_;
                                    v___y_5775_ = v_attrs_x3f_5829_;
                                    v___y_5776_ = v___y_5806_;
                                    v___y_5777_ = v_a_5819_;
                                    v___y_5778_ = v___x_5830_;
                                    v___y_5779_ = v___y_5805_;
                                    v___y_5780_ = v___y_5802_;
                                    v___y_5781_ = v___x_5825_;
                                    v___y_5782_ = v___x_5814_;
                                    v___y_5783_ = v_a_5809_;
                                    v___y_5784_ = v___y_5799_;
                                    v___y_5785_ = v_items_5812_;
                                    v___y_5786_ = v___y_5800_;
                                    v___y_5787_ = v___y_5801_;
                                    v___y_5788_ = v___y_5803_;
                                    v___y_5789_ = v_rhs_5828_;
                                    state = 20;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_a_5821_);
                                leanh::lean_dec(v_a_5819_);
                                leanh::lean_dec_ref(v_items_5812_);
                                leanh::lean_dec(v_a_5809_);
                                leanh::lean_dec(v___y_5803_);
                                leanh::lean_dec(v___y_5802_);
                                leanh::lean_dec(v___y_5801_);
                                leanh::lean_dec(v___y_5799_);
                                leanh::lean_dec(v___y_5798_);
                                leanh::lean_dec(v_x_5452_);
                                v_a_5832_ = leanh::lean_ctor_get(v___x_5822_, 0);
                                v_isSharedCheck_5839_ =
                                    (!leanh::lean_is_exclusive(v___x_5822_)) as u8;
                                if v_isSharedCheck_5839_ == 0 {
                                    v___x_5834_ = v___x_5822_;
                                    v_isShared_5835_ = v_isSharedCheck_5839_;
                                    state = 22;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5832_);
                                    leanh::lean_dec(v___x_5822_);
                                    v___x_5834_ = leanh::lean_box(0);
                                    v_isShared_5835_ = v_isSharedCheck_5839_;
                                    state = 22;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_5819_);
                            leanh::lean_dec_ref(v_items_5812_);
                            leanh::lean_dec(v_a_5809_);
                            leanh::lean_dec(v___y_5803_);
                            leanh::lean_dec(v___y_5802_);
                            leanh::lean_dec(v___y_5801_);
                            leanh::lean_dec(v___y_5799_);
                            leanh::lean_dec(v___y_5798_);
                            leanh::lean_dec(v_x_5452_);
                            v_a_5840_ = leanh::lean_ctor_get(v___x_5820_, 0);
                            v_isSharedCheck_5847_ =
                                (!leanh::lean_is_exclusive(v___x_5820_)) as u8;
                            if v_isSharedCheck_5847_ == 0 {
                                v___x_5842_ = v___x_5820_;
                                v_isShared_5843_ = v_isSharedCheck_5847_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5840_);
                                leanh::lean_dec(v___x_5820_);
                                v___x_5842_ = leanh::lean_box(0);
                                v_isShared_5843_ = v_isSharedCheck_5847_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_items_5812_);
                        leanh::lean_dec(v_a_5809_);
                        leanh::lean_dec(v___y_5803_);
                        leanh::lean_dec(v___y_5802_);
                        leanh::lean_dec(v___y_5801_);
                        leanh::lean_dec(v___y_5799_);
                        leanh::lean_dec(v___y_5798_);
                        leanh::lean_dec(v_x_5452_);
                        v_a_5848_ = leanh::lean_ctor_get(v___x_5818_, 0);
                        v_isSharedCheck_5855_ =
                            (!leanh::lean_is_exclusive(v___x_5818_)) as u8;
                        if v_isSharedCheck_5855_ == 0 {
                            v___x_5850_ = v___x_5818_;
                            v_isShared_5851_ = v_isSharedCheck_5855_;
                            state = 26;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5848_);
                            leanh::lean_dec(v___x_5818_);
                            v___x_5850_ = leanh::lean_box(0);
                            v_isShared_5851_ = v_isSharedCheck_5855_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___y_5803_);
                    leanh::lean_dec(v___y_5802_);
                    leanh::lean_dec(v___y_5801_);
                    leanh::lean_dec(v___y_5799_);
                    leanh::lean_dec(v___y_5798_);
                    leanh::lean_dec(v_x_5452_);
                    v_a_5856_ = leanh::lean_ctor_get(v___x_5808_, 0);
                    v_isSharedCheck_5863_ = (!leanh::lean_is_exclusive(v___x_5808_)) as u8;
                    if v_isSharedCheck_5863_ == 0 {
                        v___x_5858_ = v___x_5808_;
                        v_isShared_5859_ = v_isSharedCheck_5863_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5856_);
                        leanh::lean_dec(v___x_5808_);
                        v___x_5858_ = leanh::lean_box(0);
                        v_isShared_5859_ = v_isSharedCheck_5863_;
                        state = 28;
                        continue;
                    }
                }
            }
            22 => {
                if v_isShared_5835_ == 0 {
                    v___x_5837_ = v___x_5834_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_5838_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5838_, 0, v_a_5832_);
                    v___x_5837_ = v_reuseFailAlloc_5838_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_5837_;
            }
            24 => {
                if v_isShared_5843_ == 0 {
                    v___x_5845_ = v___x_5842_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_5846_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_a_5840_);
                    v___x_5845_ = v_reuseFailAlloc_5846_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_5845_;
            }
            26 => {
                if v_isShared_5851_ == 0 {
                    v___x_5853_ = v___x_5850_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
                    v___x_5853_ = v_reuseFailAlloc_5854_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_5853_;
            }
            28 => {
                if v_isShared_5859_ == 0 {
                    v___x_5861_ = v___x_5858_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5862_, 0, v_a_5856_);
                    v___x_5861_ = v_reuseFailAlloc_5862_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_5861_;
            }
            30 => {
                v___x_5875_ = leanh::lean_unsigned_to_nat(6);
                v___x_5876_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5875_);
                v___x_5877_ = l_Lean_Syntax_isNone(v___x_5876_);
                if v___x_5877_ == 0 {
                    leanh::lean_inc(v___x_5876_);
                    v___x_5878_ = l_Lean_Syntax_matchesNull(v___x_5876_, v___y_5866_);
                    if v___x_5878_ == 0 {
                        leanh::lean_dec(v___x_5876_);
                        leanh::lean_dec(v_name_x3f_5872_);
                        leanh::lean_dec(v___y_5871_);
                        leanh::lean_dec(v___y_5870_);
                        leanh::lean_dec(v___y_5867_);
                        leanh::lean_dec(v___y_5865_);
                        leanh::lean_dec(v_x_5452_);
                        v___x_5879_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                        return v___x_5879_;
                    } else {
                        v___x_5880_ = l_Lean_Syntax_getArg(v___x_5876_, v___x_5596_);
                        leanh::lean_dec(v___x_5876_);
                        v___x_5881_ = l_Lean_Elab_Command_elabNotation___closed__7;
                        leanh::lean_inc(v___x_5880_);
                        v___x_5882_ = l_Lean_Syntax_isOfKind(v___x_5880_, v___x_5881_);
                        if v___x_5882_ == 0 {
                            leanh::lean_dec(v___x_5880_);
                            leanh::lean_dec(v_name_x3f_5872_);
                            leanh::lean_dec(v___y_5871_);
                            leanh::lean_dec(v___y_5870_);
                            leanh::lean_dec(v___y_5867_);
                            leanh::lean_dec(v___y_5865_);
                            leanh::lean_dec(v_x_5452_);
                            v___x_5883_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                            return v___x_5883_;
                        } else {
                            v_prio_x3f_5884_ = l_Lean_Syntax_getArg(v___x_5880_, v___y_5868_);
                            leanh::lean_dec(v___x_5880_);
                            v___x_5885_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5885_, 0, v_prio_x3f_5884_);
                            v___y_5798_ = v___y_5865_;
                            v___y_5799_ = v___y_5867_;
                            v___y_5800_ = v___y_5869_;
                            v___y_5801_ = v___y_5870_;
                            v___y_5802_ = v_name_x3f_5872_;
                            v___y_5803_ = v___y_5871_;
                            v_prio_x3f_5804_ = v___x_5885_;
                            v___y_5805_ = v___y_5873_;
                            v___y_5806_ = v___y_5874_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5876_);
                    v___x_5886_ = leanh::lean_box(0);
                    v___y_5798_ = v___y_5865_;
                    v___y_5799_ = v___y_5867_;
                    v___y_5800_ = v___y_5869_;
                    v___y_5801_ = v___y_5870_;
                    v___y_5802_ = v_name_x3f_5872_;
                    v___y_5803_ = v___y_5871_;
                    v_prio_x3f_5804_ = v___x_5886_;
                    v___y_5805_ = v___y_5873_;
                    v___y_5806_ = v___y_5874_;
                    state = 21;
                    continue;
                }
            }
            31 => {
                v___x_5897_ = leanh::lean_unsigned_to_nat(5);
                v___x_5898_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5897_);
                v___x_5899_ = l_Lean_Syntax_isNone(v___x_5898_);
                if v___x_5899_ == 0 {
                    leanh::lean_inc(v___x_5898_);
                    v___x_5900_ = l_Lean_Syntax_matchesNull(v___x_5898_, v___y_5889_);
                    if v___x_5900_ == 0 {
                        leanh::lean_dec(v___x_5898_);
                        leanh::lean_dec(v_prec_x3f_5894_);
                        leanh::lean_dec(v___y_5893_);
                        leanh::lean_dec(v___y_5890_);
                        leanh::lean_dec(v___y_5888_);
                        leanh::lean_dec(v_x_5452_);
                        v___x_5901_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                        return v___x_5901_;
                    } else {
                        v___x_5902_ = l_Lean_Syntax_getArg(v___x_5898_, v___x_5596_);
                        leanh::lean_dec(v___x_5898_);
                        v___x_5903_ = l_Lean_Elab_Command_elabNotation___closed__10;
                        leanh::lean_inc(v___x_5902_);
                        v___x_5904_ = l_Lean_Syntax_isOfKind(v___x_5902_, v___x_5903_);
                        if v___x_5904_ == 0 {
                            leanh::lean_dec(v___x_5902_);
                            leanh::lean_dec(v_prec_x3f_5894_);
                            leanh::lean_dec(v___y_5893_);
                            leanh::lean_dec(v___y_5890_);
                            leanh::lean_dec(v___y_5888_);
                            leanh::lean_dec(v_x_5452_);
                            v___x_5905_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                            return v___x_5905_;
                        } else {
                            v_name_x3f_5906_ = l_Lean_Syntax_getArg(v___x_5902_, v___y_5891_);
                            leanh::lean_dec(v___x_5902_);
                            v___x_5907_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5907_, 0, v_name_x3f_5906_);
                            v___y_5865_ = v___y_5888_;
                            v___y_5866_ = v___y_5889_;
                            v___y_5867_ = v___y_5890_;
                            v___y_5868_ = v___y_5891_;
                            v___y_5869_ = v___y_5892_;
                            v___y_5870_ = v_prec_x3f_5894_;
                            v___y_5871_ = v___y_5893_;
                            v_name_x3f_5872_ = v___x_5907_;
                            v___y_5873_ = v___y_5895_;
                            v___y_5874_ = v___y_5896_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5898_);
                    v___x_5908_ = leanh::lean_box(0);
                    v___y_5865_ = v___y_5888_;
                    v___y_5866_ = v___y_5889_;
                    v___y_5867_ = v___y_5890_;
                    v___y_5868_ = v___y_5891_;
                    v___y_5869_ = v___y_5892_;
                    v___y_5870_ = v_prec_x3f_5894_;
                    v___y_5871_ = v___y_5893_;
                    v_name_x3f_5872_ = v___x_5908_;
                    v___y_5873_ = v___y_5895_;
                    v___y_5874_ = v___y_5896_;
                    state = 30;
                    continue;
                }
            }
            32 => {
                v___x_5915_ = leanh::lean_unsigned_to_nat(2);
                v_attrKind_5916_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5915_);
                v___x_5917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__2;
                v___x_5918_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_addInheritDocDefault_spec__0___closed__6;
                leanh::lean_inc(v_attrKind_5916_);
                v___x_5919_ = l_Lean_Syntax_isOfKind(v_attrKind_5916_, v___x_5918_);
                if v___x_5919_ == 0 {
                    leanh::lean_dec(v_attrKind_5916_);
                    leanh::lean_dec(v_attrs_x3f_5912_);
                    leanh::lean_dec(v___y_5911_);
                    leanh::lean_dec(v_x_5452_);
                    v___x_5920_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                    return v___x_5920_;
                } else {
                    v___x_5921_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5922_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5923_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5922_);
                    v___x_5924_ = l_Lean_Syntax_isNone(v___x_5923_);
                    if v___x_5924_ == 0 {
                        leanh::lean_inc(v___x_5923_);
                        v___x_5925_ = l_Lean_Syntax_matchesNull(v___x_5923_, v___y_5910_);
                        if v___x_5925_ == 0 {
                            leanh::lean_dec(v___x_5923_);
                            leanh::lean_dec(v_attrKind_5916_);
                            leanh::lean_dec(v_attrs_x3f_5912_);
                            leanh::lean_dec(v___y_5911_);
                            leanh::lean_dec(v_x_5452_);
                            v___x_5926_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                            return v___x_5926_;
                        } else {
                            v___x_5927_ = l_Lean_Syntax_getArg(v___x_5923_, v___x_5596_);
                            leanh::lean_dec(v___x_5923_);
                            v___x_5928_ =
                                l_Lean_Elab_Command_expandNotationItemIntoSyntaxItem___closed__5;
                            leanh::lean_inc(v___x_5927_);
                            v___x_5929_ = l_Lean_Syntax_isOfKind(v___x_5927_, v___x_5928_);
                            if v___x_5929_ == 0 {
                                leanh::lean_dec(v___x_5927_);
                                leanh::lean_dec(v_attrKind_5916_);
                                leanh::lean_dec(v_attrs_x3f_5912_);
                                leanh::lean_dec(v___y_5911_);
                                leanh::lean_dec(v_x_5452_);
                                v___x_5930_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                                return v___x_5930_;
                            } else {
                                v_prec_x3f_5931_ = l_Lean_Syntax_getArg(v___x_5927_, v___y_5910_);
                                leanh::lean_dec(v___x_5927_);
                                v___x_5932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_5932_, 0, v_prec_x3f_5931_);
                                v___y_5888_ = v_attrs_x3f_5912_;
                                v___y_5889_ = v___y_5910_;
                                v___y_5890_ = v___y_5911_;
                                v___y_5891_ = v___x_5921_;
                                v___y_5892_ = v___x_5917_;
                                v___y_5893_ = v_attrKind_5916_;
                                v_prec_x3f_5894_ = v___x_5932_;
                                v___y_5895_ = v___y_5913_;
                                v___y_5896_ = v___y_5914_;
                                state = 31;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_5923_);
                        v___x_5933_ = leanh::lean_box(0);
                        v___y_5888_ = v_attrs_x3f_5912_;
                        v___y_5889_ = v___y_5910_;
                        v___y_5890_ = v___y_5911_;
                        v___y_5891_ = v___x_5921_;
                        v___y_5892_ = v___x_5917_;
                        v___y_5893_ = v_attrKind_5916_;
                        v_prec_x3f_5894_ = v___x_5933_;
                        v___y_5895_ = v___y_5913_;
                        v___y_5896_ = v___y_5914_;
                        state = 31;
                        continue;
                    }
                }
            }
            33 => {
                v___x_5938_ = leanh::lean_unsigned_to_nat(1);
                v___x_5939_ = l_Lean_Syntax_getArg(v_x_5452_, v___x_5938_);
                v___x_5940_ = l_Lean_Syntax_isNone(v___x_5939_);
                if v___x_5940_ == 0 {
                    leanh::lean_inc(v___x_5939_);
                    v___x_5941_ = l_Lean_Syntax_matchesNull(v___x_5939_, v___x_5938_);
                    if v___x_5941_ == 0 {
                        leanh::lean_dec(v___x_5939_);
                        leanh::lean_dec(v_doc_x3f_5935_);
                        leanh::lean_dec(v_x_5452_);
                        v___x_5942_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                        return v___x_5942_;
                    } else {
                        v___x_5943_ = l_Lean_Syntax_getArg(v___x_5939_, v___x_5596_);
                        leanh::lean_dec(v___x_5939_);
                        v___x_5944_ = l_Lean_Elab_Command_mkUnexpander___closed__12;
                        leanh::lean_inc(v___x_5943_);
                        v___x_5945_ = l_Lean_Syntax_isOfKind(v___x_5943_, v___x_5944_);
                        if v___x_5945_ == 0 {
                            leanh::lean_dec(v___x_5943_);
                            leanh::lean_dec(v_doc_x3f_5935_);
                            leanh::lean_dec(v_x_5452_);
                            v___x_5946_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabNotation_spec__0___redArg();
                            return v___x_5946_;
                        } else {
                            v___x_5947_ = l_Lean_Syntax_getArg(v___x_5943_, v___x_5938_);
                            leanh::lean_dec(v___x_5943_);
                            v_attrs_x3f_5948_ = l_Lean_Syntax_getArgs(v___x_5947_);
                            leanh::lean_dec(v___x_5947_);
                            v___x_5949_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_5949_, 0, v_attrs_x3f_5948_);
                            v___y_5910_ = v___x_5938_;
                            v___y_5911_ = v_doc_x3f_5935_;
                            v_attrs_x3f_5912_ = v___x_5949_;
                            v___y_5913_ = v___y_5936_;
                            v___y_5914_ = v___y_5937_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_5939_);
                    v___x_5950_ = leanh::lean_box(0);
                    v___y_5910_ = v___x_5938_;
                    v___y_5911_ = v_doc_x3f_5935_;
                    v_attrs_x3f_5912_ = v___x_5950_;
                    v___y_5913_ = v___y_5936_;
                    v___y_5914_ = v___y_5937_;
                    state = 32;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabNotation___boxed(
    mut v_x_5962_: *mut leanh::LeanObject,
    mut v_a_5963_: *mut leanh::LeanObject,
    mut v_a_5964_: *mut leanh::LeanObject,
    mut v_a_5965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5966_ = l_Lean_Elab_Command_elabNotation(v_x_5962_, v_a_5963_, v_a_5964_);
    leanh::lean_dec(v_a_5964_);
    leanh::lean_dec_ref(v_a_5963_);
    return v_res_5966_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(
    mut v_00_u03b1_5967_: *mut leanh::LeanObject,
    mut v_x_5968_: *mut leanh::LeanObject,
    mut v___y_5969_: *mut leanh::LeanObject,
    mut v___y_5970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5971_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___redArg(v_x_5968_, v___y_5970_);
    return v___x_5971_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2___boxed(
    mut v_00_u03b1_5972_: *mut leanh::LeanObject,
    mut v_x_5973_: *mut leanh::LeanObject,
    mut v___y_5974_: *mut leanh::LeanObject,
    mut v___y_5975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5976_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__2(v_00_u03b1_5972_, v_x_5973_, v___y_5974_, v___y_5975_);
    leanh::lean_dec_ref(v___y_5974_);
    leanh::lean_dec_ref(v_x_5973_);
    return v_res_5976_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(
    mut v_00_u03b1_5977_: *mut leanh::LeanObject,
    mut v_ref_5978_: *mut leanh::LeanObject,
    mut v___y_5979_: *mut leanh::LeanObject,
    mut v___y_5980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5982_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___redArg(v_ref_5978_);
    return v___x_5982_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7___boxed(
    mut v_00_u03b1_5983_: *mut leanh::LeanObject,
    mut v_ref_5984_: *mut leanh::LeanObject,
    mut v___y_5985_: *mut leanh::LeanObject,
    mut v___y_5986_: *mut leanh::LeanObject,
    mut v___y_5987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5988_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__7(v_00_u03b1_5983_, v_ref_5984_, v___y_5985_, v___y_5986_);
    leanh::lean_dec(v___y_5986_);
    leanh::lean_dec_ref(v___y_5985_);
    return v_res_5988_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(
    mut v_00_u03b1_5989_: *mut leanh::LeanObject,
    mut v_x_5990_: *mut leanh::LeanObject,
    mut v___y_5991_: *mut leanh::LeanObject,
    mut v___y_5992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5994_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___redArg(
        v_x_5990_,
        v___y_5991_,
        v___y_5992_,
    );
    return v___x_5994_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1___boxed(
    mut v_00_u03b1_5995_: *mut leanh::LeanObject,
    mut v_x_5996_: *mut leanh::LeanObject,
    mut v___y_5997_: *mut leanh::LeanObject,
    mut v___y_5998_: *mut leanh::LeanObject,
    mut v___y_5999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6000_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1(
        v_00_u03b1_5995_,
        v_x_5996_,
        v___y_5997_,
        v___y_5998_,
    );
    leanh::lean_dec(v___y_5998_);
    leanh::lean_dec_ref(v___y_5997_);
    return v_res_6000_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(
    mut v_msgData_6001_: *mut leanh::LeanObject,
    mut v___y_6002_: *mut leanh::LeanObject,
    mut v___y_6003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6005_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___redArg(v_msgData_6001_, v___y_6003_);
    return v___x_6005_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3___boxed(
    mut v_msgData_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
    mut v___y_6009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6010_ = l_Lean_addMessageContextPartial___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__1_spec__3(v_msgData_6006_, v___y_6007_, v___y_6008_);
    leanh::lean_dec(v___y_6008_);
    leanh::lean_dec_ref(v___y_6007_);
    return v_res_6010_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(
    mut v_as_6011_: *mut leanh::LeanObject,
    mut v_as_x27_6012_: *mut leanh::LeanObject,
    mut v_b_6013_: *mut leanh::LeanObject,
    mut v_a_6014_: *mut leanh::LeanObject,
    mut v___y_6015_: *mut leanh::LeanObject,
    mut v___y_6016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6018_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___redArg(v_as_x27_6012_, v_b_6013_, v___y_6015_, v___y_6016_);
    return v___x_6018_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4___boxed(
    mut v_as_6019_: *mut leanh::LeanObject,
    mut v_as_x27_6020_: *mut leanh::LeanObject,
    mut v_b_6021_: *mut leanh::LeanObject,
    mut v_a_6022_: *mut leanh::LeanObject,
    mut v___y_6023_: *mut leanh::LeanObject,
    mut v___y_6024_: *mut leanh::LeanObject,
    mut v___y_6025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6026_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__4(v_as_6019_, v_as_x27_6020_, v_b_6021_, v_a_6022_, v___y_6023_, v___y_6024_);
    leanh::lean_dec(v___y_6024_);
    leanh::lean_dec_ref(v___y_6023_);
    leanh::lean_dec(v_as_x27_6020_);
    leanh::lean_dec(v_as_6019_);
    return v_res_6026_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(
    mut v_00_u03b1_6027_: *mut leanh::LeanObject,
    mut v_ref_6028_: *mut leanh::LeanObject,
    mut v_msg_6029_: *mut leanh::LeanObject,
    mut v___y_6030_: *mut leanh::LeanObject,
    mut v___y_6031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6033_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___redArg(v_ref_6028_, v_msg_6029_, v___y_6030_, v___y_6031_);
    return v___x_6033_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6___boxed(
    mut v_00_u03b1_6034_: *mut leanh::LeanObject,
    mut v_ref_6035_: *mut leanh::LeanObject,
    mut v_msg_6036_: *mut leanh::LeanObject,
    mut v___y_6037_: *mut leanh::LeanObject,
    mut v___y_6038_: *mut leanh::LeanObject,
    mut v___y_6039_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6040_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6(v_00_u03b1_6034_, v_ref_6035_, v_msg_6036_, v___y_6037_, v___y_6038_);
    leanh::lean_dec(v___y_6038_);
    leanh::lean_dec_ref(v___y_6037_);
    leanh::lean_dec(v_ref_6035_);
    return v_res_6040_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(
    mut v_00_u03b2_6041_: *mut leanh::LeanObject,
    mut v_m_6042_: *mut leanh::LeanObject,
    mut v_a_6043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6044_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___redArg(v_m_6042_, v_a_6043_);
    return v___x_6044_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8___boxed(
    mut v_00_u03b2_6045_: *mut leanh::LeanObject,
    mut v_m_6046_: *mut leanh::LeanObject,
    mut v_a_6047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6048_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8(v_00_u03b2_6045_, v_m_6046_, v_a_6047_);
    leanh::lean_dec(v_a_6047_);
    leanh::lean_dec_ref(v_m_6046_);
    return v_res_6048_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(
    mut v_00_u03b1_6049_: *mut leanh::LeanObject,
    mut v_msg_6050_: *mut leanh::LeanObject,
    mut v___y_6051_: *mut leanh::LeanObject,
    mut v___y_6052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6054_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___redArg(v_msg_6050_, v___y_6051_, v___y_6052_);
    return v___x_6054_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12___boxed(
    mut v_00_u03b1_6055_: *mut leanh::LeanObject,
    mut v_msg_6056_: *mut leanh::LeanObject,
    mut v___y_6057_: *mut leanh::LeanObject,
    mut v___y_6058_: *mut leanh::LeanObject,
    mut v___y_6059_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6060_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12(v_00_u03b1_6055_, v_msg_6056_, v___y_6057_, v___y_6058_);
    leanh::lean_dec(v___y_6058_);
    leanh::lean_dec_ref(v___y_6057_);
    return v_res_6060_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(
    mut v_00_u03b2_6061_: *mut leanh::LeanObject,
    mut v_x_6062_: *mut leanh::LeanObject,
    mut v_x_6063_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6064_: u8 = 0;
    v___x_6064_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___redArg(v_x_6062_, v_x_6063_);
    return v___x_6064_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15___boxed(
    mut v_00_u03b2_6065_: *mut leanh::LeanObject,
    mut v_x_6066_: *mut leanh::LeanObject,
    mut v_x_6067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6068_: u8 = 0;
    let mut v_r_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6068_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15(v_00_u03b2_6065_, v_x_6066_, v_x_6067_);
    leanh::lean_dec_ref(v_x_6067_);
    leanh::lean_dec_ref(v_x_6066_);
    v_r_6069_ = leanh::lean_box((v_res_6068_) as usize);
    return v_r_6069_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(
    mut v_00_u03b2_6070_: *mut leanh::LeanObject,
    mut v_a_6071_: *mut leanh::LeanObject,
    mut v_x_6072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6073_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___redArg(v_a_6071_, v_x_6072_);
    return v___x_6073_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18___boxed(
    mut v_00_u03b2_6074_: *mut leanh::LeanObject,
    mut v_a_6075_: *mut leanh::LeanObject,
    mut v_x_6076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6077_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__8_spec__18(v_00_u03b2_6074_, v_a_6075_, v_x_6076_);
    leanh::lean_dec(v_x_6076_);
    leanh::lean_dec(v_a_6075_);
    return v_res_6077_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(
    mut v_msgData_6078_: *mut leanh::LeanObject,
    mut v_macroStack_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6083_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___redArg(v_msgData_6078_, v_macroStack_6079_, v___y_6081_);
    return v___x_6083_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23___boxed(
    mut v_msgData_6084_: *mut leanh::LeanObject,
    mut v_macroStack_6085_: *mut leanh::LeanObject,
    mut v___y_6086_: *mut leanh::LeanObject,
    mut v___y_6087_: *mut leanh::LeanObject,
    mut v___y_6088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6089_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__6_spec__12_spec__23(v_msgData_6084_, v_macroStack_6085_, v___y_6086_, v___y_6087_);
    leanh::lean_dec(v___y_6087_);
    leanh::lean_dec_ref(v___y_6086_);
    return v_res_6089_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(
    mut v_00_u03b2_6090_: *mut leanh::LeanObject,
    mut v_x_6091_: *mut leanh::LeanObject,
    mut v_x_6092_: usize,
    mut v_x_6093_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6094_: u8 = 0;
    v___x_6094_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___redArg(v_x_6091_, v_x_6092_, v_x_6093_);
    return v___x_6094_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19___boxed(
    mut v_00_u03b2_6095_: *mut leanh::LeanObject,
    mut v_x_6096_: *mut leanh::LeanObject,
    mut v_x_6097_: *mut leanh::LeanObject,
    mut v_x_6098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_25613__boxed_6099_: usize = 0;
    let mut v_res_6100_: u8 = 0;
    let mut v_r_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_25613__boxed_6099_ = leanh::lean_unbox_usize(v_x_6097_);
    leanh::lean_dec(v_x_6097_);
    v_res_6100_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19(v_00_u03b2_6095_, v_x_6096_, v_x_25613__boxed_6099_, v_x_6098_);
    leanh::lean_dec_ref(v_x_6098_);
    leanh::lean_dec_ref(v_x_6096_);
    v_r_6101_ = leanh::lean_box((v_res_6100_) as usize);
    return v_r_6101_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(
    mut v_00_u03b2_6102_: *mut leanh::LeanObject,
    mut v_keys_6103_: *mut leanh::LeanObject,
    mut v_vals_6104_: *mut leanh::LeanObject,
    mut v_heq_6105_: *mut leanh::LeanObject,
    mut v_i_6106_: *mut leanh::LeanObject,
    mut v_k_6107_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6108_: u8 = 0;
    v___x_6108_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___redArg(v_keys_6103_, v_i_6106_, v_k_6107_);
    return v___x_6108_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23___boxed(
    mut v_00_u03b2_6109_: *mut leanh::LeanObject,
    mut v_keys_6110_: *mut leanh::LeanObject,
    mut v_vals_6111_: *mut leanh::LeanObject,
    mut v_heq_6112_: *mut leanh::LeanObject,
    mut v_i_6113_: *mut leanh::LeanObject,
    mut v_k_6114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6115_: u8 = 0;
    let mut v_r_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6115_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabNotation_spec__1_spec__3_spec__6_spec__15_spec__19_spec__23(v_00_u03b2_6109_, v_keys_6110_, v_vals_6111_, v_heq_6112_, v_i_6113_, v_k_6114_);
    leanh::lean_dec_ref(v_k_6114_);
    leanh::lean_dec_ref(v_vals_6111_);
    leanh::lean_dec_ref(v_keys_6110_);
    v_r_6116_ = leanh::lean_box((v_res_6115_) as usize);
    return v_r_6116_;
}
pub unsafe fn l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1()
-> *mut leanh::LeanObject {
    let mut v___x_6124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6124_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_6125_ = l_Lean_Elab_Command_elabNotation___closed__1;
    v___x_6126_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___closed__1;
    v___x_6127_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabNotation___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_6128_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6124_,
        v___x_6125_,
        v___x_6126_,
        v___x_6127_,
    );
    return v___x_6128_;
}
pub unsafe fn l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1___boxed(
    mut v_a_6129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6130_ = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
    return v_res_6130_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Notation(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_AuxDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Notation_0__Lean_Elab_Command_elabNotation___regBuiltin_Lean_Elab_Command_elabNotation__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Notation(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Notation(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Syntax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_AuxDef(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_BuiltinNotation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Notation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Notation(builtin);
}