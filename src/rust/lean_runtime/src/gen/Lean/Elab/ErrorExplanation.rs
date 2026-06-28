// Lean compiler output
// Module: Lean.Elab.ErrorExplanation
// Imports: Lean.Widget.UserWidget Lean.Widget.UserWidget
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Meta::Defs::{
    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f, l_Lean_Syntax_mkNameLit,
    l_Lean_TSyntax_getId, l_Lean_quoteNameMk,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Macro_throwUnsupported___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hasMacroScopes, l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1,
    l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_SourceInfo_fromRef,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getId, l_Lean_Syntax_getKind,
    l_Lean_Syntax_getNumArgs, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node2, l_Lean_Syntax_node3,
    l_Lean_addMacroScope, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
    l_String_toRawSubstring_x27, lean_erase_macro_scopes,
};
use crate::r#gen::Init::Syntax::l_Lean_Syntax_setArgs;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Lsp::Utf16::l_Lean_DeclarationRange_ofStringPositions;
use crate::r#gen::Lean::Data::Name::{l_Lean_Name_getNumParts, l_Lean_Name_isAnonymous};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_commandElabAttribute, l_Lean_Elab_Command_getRef___redArg,
    l_Lean_Elab_Command_runTermElabM___redArg,
};
use crate::r#gen::Lean::Elab::Exception::{
    l_Lean_Elab_abortTermExceptionId, l_Lean_Elab_unsupportedSyntaxExceptionId,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_elabTerm, l_Lean_Elab_Term_elabTermEnsuringType,
    l_Lean_Elab_Term_termElabAttribute,
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
use crate::r#gen::Lean::ErrorExplanation::l_Lean_errorExplanationExt;
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed,
    l_Lean_errorDescriptionWidget, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_hint_x27,
    l_Lean_MessageData_note, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Eval::l_Lean_Meta_evalExpr___redArg;
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Util::Sorry::l_Lean_Expr_hasSyntheticSorry;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
};
use crate::r#gen::Lean::Widget::UserWidget::{
    initialize_Lean_Widget_UserWidget, l_Lean_Widget_addBuiltinModule,
    runtime_initialize_Lean_Widget_UserWidget,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
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
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_sub, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [101, 114, 114, 111, 114, 68, 101, 115, 99, 114, 105, 112, 116, 105, 111, 110, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value) as *mut crate::leanh::LeanObject,11821295174094476641 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value:
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value:
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
    m_data: [84, 101, 114, 109, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value:
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
        116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 77, 97, 99, 114,
        111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7097802073468323731 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65, 116, 77, 97,
        99, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value)
            as *mut crate::leanh::LeanObject,
        3360895518896177531 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 77, 97, 99, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9653194137920487497 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65, 116, 77, 97, 99, 114,
        111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value)
            as *mut crate::leanh::LeanObject,
        12924865489819135822 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110, 103, 77, 97, 99, 114,
        111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value)
            as *mut crate::leanh::LeanObject,
        13287924405428050690 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110, 103, 65, 116, 77, 97, 99,
        114, 111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value)
            as *mut crate::leanh::LeanObject,
        16765905629307186191 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value:
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
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100,
        0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value)
            as *mut crate::leanh::LeanObject,
        14298422259736409839 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value:
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 46, 108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110,
        103, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110, 103, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value)
            as *mut crate::leanh::LeanObject,
        17497790286802646181 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value:
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
    m_data: [110, 117, 108, 108, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value:
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
    m_data: [113, 117, 111, 116, 101, 100, 78, 97, 109, 101, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value)
            as *mut crate::leanh::LeanObject,
        9368229134555052249 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value:
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
    m_data: [96, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value:
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
    m_data: [46, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value:
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
    m_data: [116, 101, 114, 109, 77, 33, 95, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value)
            as *mut crate::leanh::LeanObject,
        13317951319906582257 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value:
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
    m_data: [109, 33, 0],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value:
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
        76, 101, 97, 110, 46, 108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110,
        103, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value)
            as *mut crate::leanh::LeanObject,
        17298265491216151842 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value:
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
        76, 101, 97, 110, 46, 108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65,
        116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value)
            as *mut crate::leanh::LeanObject,
        6024285242114364631 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value:
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
        76, 101, 97, 110, 46, 108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value:
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value)
            as *mut crate::leanh::LeanObject,
        14450959914897649857 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        76, 101, 97, 110, 46, 116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111,
        114, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value:
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
        116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value)
            as *mut crate::leanh::LeanObject,
        8567430786828469655 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value:
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value)
            as *mut crate::leanh::LeanObject,
        5117844058249666356 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value:
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
        76, 101, 97, 110, 46, 116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111,
        114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value:
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
        116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value:
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value)
            as *mut crate::leanh::LeanObject,
        8906461912520152887 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64_value:
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64_value)
        as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 120, 99, 101, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value) as *mut crate::leanh::LeanObject,16971822718086795385 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [76, 111, 103, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value) as *mut crate::leanh::LeanObject,15983123899464659095 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0_value:
    crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject {
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
        84, 104, 101, 32, 101, 114, 114, 111, 114, 32, 110, 97, 109, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2_value:
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
        96, 32, 119, 97, 115, 32, 114, 101, 109, 111, 118, 101, 100, 32, 105, 110, 32, 76, 101, 97,
        110, 32, 118, 101, 114, 115, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 25,
    m_capacity: 25,
    m_length: 24,
    m_data: [
        32, 97, 110, 100, 32, 115, 104, 111, 117, 108, 100, 32, 110, 111, 116, 32, 98, 101, 32,
        117, 115, 101, 100, 46, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6_value:
    crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 51,
    m_capacity: 51,
    m_length: 50,
    m_data: [
        84, 104, 101, 114, 101, 32, 105, 115, 32, 110, 111, 32, 101, 120, 112, 108, 97, 110, 97,
        116, 105, 111, 110, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 119, 105,
        116, 104, 32, 116, 104, 101, 32, 110, 97, 109, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8_value:
    crate::leanh::LeanStringObject<81> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 81,
    m_capacity: 81,
    m_length: 80,
    m_data: [
        96, 46, 32, 82, 101, 103, 105, 115, 116, 101, 114, 32, 97, 110, 32, 101, 120, 112, 108, 97,
        110, 97, 116, 105, 111, 110, 32, 102, 111, 114, 32, 116, 104, 105, 115, 32, 101, 114, 114,
        111, 114, 32, 105, 110, 32, 116, 104, 101, 32, 96, 76, 101, 97, 110, 46, 69, 114, 114, 111,
        114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 96, 32, 109, 111, 100, 117, 108,
        101, 46, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10_value:
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
        84, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12_value:
    crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        96, 32, 104, 97, 115, 32, 110, 111, 116, 32, 98, 101, 101, 110, 32, 105, 109, 112, 111,
        114, 116, 101, 100, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14_value:
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
    m_data: [65, 100, 100, 32, 96, 105, 109, 112, 111, 114, 116, 32, 0],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16_value:
    crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        96, 32, 116, 111, 32, 116, 104, 105, 115, 32, 102, 105, 108, 101, 39, 115, 32, 104, 101,
        97, 100, 101, 114, 32, 116, 111, 32, 117, 115, 101, 32, 116, 104, 105, 115, 32, 109, 97,
        99, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 67, 104, 101, 99, 107, 101, 100, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut crate::leanh::LeanObject,13311307985783427614 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value) as *mut crate::leanh::LeanObject,5305096624820345885 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value:
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value:
    crate::leanh::LeanStringObject<28> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110,
        97, 116, 105, 111, 110, 83, 116, 120, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        18241697017225771414 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value:
    crate::leanh::LeanStringObject<66> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 66,
    m_capacity: 66,
    m_length: 65,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 101, 120, 112, 108, 97, 110, 97, 116,
        105, 111, 110, 58, 32, 65, 110, 32, 101, 114, 114, 111, 114, 32, 101, 120, 112, 108, 97,
        110, 97, 116, 105, 111, 110, 32, 97, 108, 114, 101, 97, 100, 121, 32, 101, 120, 105, 115,
        116, 115, 32, 102, 111, 114, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_value:
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
        73, 110, 118, 97, 108, 105, 100, 32, 110, 97, 109, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_value:
    crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 52,
    m_capacity: 52,
    m_length: 51,
    m_data: [
        96, 58, 32, 69, 114, 114, 111, 114, 32, 101, 120, 112, 108, 97, 110, 97, 116, 105, 111,
        110, 32, 110, 97, 109, 101, 115, 32, 109, 117, 115, 116, 32, 104, 97, 118, 101, 32, 116,
        119, 111, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116, 115, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_value:
    crate::leanh::LeanStringObject<149> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 149,
    m_capacity: 149,
    m_length: 148,
    m_data: [
        84, 104, 101, 32, 102, 105, 114, 115, 116, 32, 99, 111, 109, 112, 111, 110, 101, 110, 116,
        32, 111, 102, 32, 97, 110, 32, 101, 114, 114, 111, 114, 32, 101, 120, 112, 108, 97, 110,
        97, 116, 105, 111, 110, 32, 110, 97, 109, 101, 32, 105, 100, 101, 110, 116, 105, 102, 105,
        101, 115, 32, 116, 104, 101, 32, 112, 97, 99, 107, 97, 103, 101, 32, 102, 114, 111, 109,
        32, 119, 104, 105, 99, 104, 32, 116, 104, 101, 32, 101, 114, 114, 111, 114, 32, 111, 114,
        105, 103, 105, 110, 97, 116, 101, 115, 44, 32, 97, 110, 100, 32, 116, 104, 101, 32, 115,
        101, 99, 111, 110, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 115, 32, 116, 104,
        101, 32, 101, 114, 114, 111, 114, 32, 105, 116, 115, 101, 108, 102, 46, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_value:
    crate::leanh::LeanStringObject<132> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 132,
    m_capacity: 132,
    m_length: 131,
    m_data: [
        96, 58, 32, 69, 114, 114, 111, 114, 32, 101, 120, 112, 108, 97, 110, 97, 116, 105, 111,
        110, 115, 32, 99, 97, 110, 110, 111, 116, 32, 104, 97, 118, 101, 32, 105, 110, 97, 99, 99,
        101, 115, 115, 105, 98, 108, 101, 32, 110, 97, 109, 101, 115, 46, 32, 84, 104, 105, 115,
        32, 101, 114, 114, 111, 114, 32, 111, 102, 116, 101, 110, 32, 111, 99, 99, 117, 114, 115,
        32, 119, 104, 101, 110, 32, 97, 110, 32, 101, 114, 114, 111, 114, 32, 101, 120, 112, 108,
        97, 110, 97, 116, 105, 111, 110, 32, 105, 115, 32, 103, 101, 110, 101, 114, 97, 116, 101,
        100, 32, 117, 115, 105, 110, 103, 32, 97, 32, 109, 97, 99, 114, 111, 46, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value:
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
    m_data: [77, 101, 116, 97, 100, 97, 116, 97, 0],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut crate::leanh::LeanObject,18239673213070638308 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value
        ) as *mut crate::leanh::LeanObject,
        16597581185784988388 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_value:
    crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 38,
    m_capacity: 38,
    m_length: 37,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 110, 97, 109, 101, 32, 102, 111, 114, 32, 101, 114,
        114, 111, 114, 32, 101, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 58, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_value:
    crate::leanh::LeanStringObject<83> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 83,
    m_capacity: 83,
    m_length: 82,
    m_data: [
        84, 111, 32, 117, 115, 101, 32, 116, 104, 105, 115, 32, 99, 111, 109, 109, 97, 110, 100,
        44, 32, 97, 100, 100, 32, 96, 105, 109, 112, 111, 114, 116, 32, 76, 101, 97, 110, 46, 69,
        114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 96, 32, 116, 111,
        32, 116, 104, 101, 32, 104, 101, 97, 100, 101, 114, 32, 111, 102, 32, 116, 104, 105, 115,
        32, 102, 105, 108, 101, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [101, 108, 97, 98, 82, 101, 103, 105, 115, 116, 101, 114, 69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut crate::leanh::LeanObject,13311307985783427614 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value) as *mut crate::leanh::LeanObject,2761648309649773589 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3592_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2;
    v___x_3593_ = l_Lean_errorDescriptionWidget;
    v___x_3594_ = l_Lean_Widget_addBuiltinModule(v___x_3592_, v___x_3593_);
    return v___x_3594_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___boxed(
    mut v_a_3595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3596_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
    return v_res_3596_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3645_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
    v___x_3646_ = l_String_toRawSubstring_x27(v___x_3645_);
    return v___x_3646_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3674_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
    v___x_3675_ = l_String_toRawSubstring_x27(v___x_3674_);
    return v___x_3675_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
    v___x_3688_ = l_String_toRawSubstring_x27(v___x_3687_);
    return v___x_3688_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
    v___x_3701_ = l_String_toRawSubstring_x27(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3713_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
    v___x_3714_ = l_String_toRawSubstring_x27(v___x_3713_);
    return v___x_3714_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
    v___x_3730_ = l_String_toRawSubstring_x27(v___x_3729_);
    return v___x_3730_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(
    mut v_x_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: u8 = 0;
    let mut v_quotContext_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v_quotContext_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: u8 = 0;
    let mut v_quotContext_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: u8 = 0;
    let mut v_quotContext_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v_quotContext_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: u8 = 0;
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: u8 = 0;
    let mut v_quotContext_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3744_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
                crate::leanh::lean_inc(v_x_3741_);
                v___x_3745_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3744_);
                if v___x_3745_ == 0 {
                    v___x_3746_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
                    crate::leanh::lean_inc(v_x_3741_);
                    v___x_3747_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3746_);
                    if v___x_3747_ == 0 {
                        v___x_3748_ =
                            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
                        crate::leanh::lean_inc(v_x_3741_);
                        v___x_3749_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3748_);
                        if v___x_3749_ == 0 {
                            v___x_3750_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
                            crate::leanh::lean_inc(v_x_3741_);
                            v___x_3751_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3750_);
                            if v___x_3751_ == 0 {
                                v___x_3752_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
                                crate::leanh::lean_inc(v_x_3741_);
                                v___x_3753_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3752_);
                                if v___x_3753_ == 0 {
                                    v___x_3754_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
                                    crate::leanh::lean_inc(v_x_3741_);
                                    v___x_3755_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3754_);
                                    if v___x_3755_ == 0 {
                                        crate::leanh::lean_dec(v_x_3741_);
                                        v___x_3756_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                        return v___x_3756_;
                                    } else {
                                        v___x_3757_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v___x_3758_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_3759_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3758_);
                                        v___x_3760_ =
                                            l_Lean_Syntax_matchesNull(v___x_3759_, v___x_3757_);
                                        if v___x_3760_ == 0 {
                                            crate::leanh::lean_dec(v_x_3741_);
                                            v___x_3761_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                            return v___x_3761_;
                                        } else {
                                            v___x_3762_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_3763_ =
                                                l_Lean_Syntax_getArg(v_x_3741_, v___x_3762_);
                                            v___x_3764_ = crate::leanh::lean_unsigned_to_nat(2);
                                            v_id_3765_ =
                                                l_Lean_Syntax_getArg(v_x_3741_, v___x_3764_);
                                            v___x_3766_ = crate::leanh::lean_unsigned_to_nat(4);
                                            v___x_3767_ =
                                                l_Lean_Syntax_getArg(v_x_3741_, v___x_3766_);
                                            crate::leanh::lean_dec(v_x_3741_);
                                            v___x_3768_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                            crate::leanh::lean_inc(v___x_3767_);
                                            v___x_3769_ =
                                                l_Lean_Syntax_isOfKind(v___x_3767_, v___x_3768_);
                                            if v___x_3769_ == 0 {
                                                v_quotContext_3770_ =
                                                    crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                                v_currMacroScope_3771_ =
                                                    crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                                v_ref_3772_ =
                                                    crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                                v___x_3773_ = l_Lean_SourceInfo_fromRef(
                                                    v_ref_3772_,
                                                    v___x_3769_,
                                                );
                                                v___x_3774_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                                v___x_3775_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
                                                v___x_3776_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
                                                crate::leanh::lean_inc(v_currMacroScope_3771_);
                                                crate::leanh::lean_inc(v_quotContext_3770_);
                                                v___x_3777_ = l_Lean_addMacroScope(
                                                    v_quotContext_3770_,
                                                    v___x_3776_,
                                                    v_currMacroScope_3771_,
                                                );
                                                v___x_3778_ = crate::leanh::lean_box(0);
                                                v___x_3779_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
                                                crate::leanh::lean_inc(v___x_3773_);
                                                v___x_3780_ =
                                                    crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3780_,
                                                    0,
                                                    v___x_3773_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3780_,
                                                    1,
                                                    v___x_3775_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3780_,
                                                    2,
                                                    v___x_3777_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3780_,
                                                    3,
                                                    v___x_3779_,
                                                );
                                                v___x_3781_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                                v___x_3787_ = l_Lean_TSyntax_getId(v_id_3765_);
                                                crate::leanh::lean_dec(v_id_3765_);
                                                crate::leanh::lean_inc(v___x_3787_);
                                                v___x_3788_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3778_, v___x_3787_);
                                                if crate::leanh::lean_obj_tag(v___x_3788_) == 0 {
                                                    v___x_3789_ = l_Lean_quoteNameMk(v___x_3787_);
                                                    v___y_3783_ = v___x_3789_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_3787_);
                                                    v_val_3790_ =
                                                        crate::leanh::lean_ctor_get(v___x_3788_, 0);
                                                    crate::leanh::lean_inc(v_val_3790_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3788_,
                                                        1,
                                                    );
                                                    v___x_3791_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                                    v___x_3792_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                                    v___x_3793_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                                    v___x_3794_ = lean_string_intercalate(
                                                        v___x_3793_,
                                                        v_val_3790_,
                                                    );
                                                    v___x_3795_ = lean_string_append(
                                                        v___x_3792_,
                                                        v___x_3794_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_3794_);
                                                    v___x_3796_ = crate::leanh::lean_box(2);
                                                    v___x_3797_ = l_Lean_Syntax_mkNameLit(
                                                        v___x_3795_,
                                                        v___x_3796_,
                                                    );
                                                    v___x_3798_ = lean_mk_empty_array_with_capacity(
                                                        v___x_3762_,
                                                    );
                                                    v___x_3799_ =
                                                        lean_array_push(v___x_3798_, v___x_3797_);
                                                    v___x_3800_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        3,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3800_,
                                                        0,
                                                        v___x_3796_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3800_,
                                                        1,
                                                        v___x_3791_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3800_,
                                                        2,
                                                        v___x_3799_,
                                                    );
                                                    v___y_3783_ = v___x_3800_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v_quotContext_3801_ =
                                                    crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                                v_currMacroScope_3802_ =
                                                    crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                                v_ref_3803_ =
                                                    crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                                v___x_3804_ = l_Lean_SourceInfo_fromRef(
                                                    v_ref_3803_,
                                                    v___x_3753_,
                                                );
                                                v___x_3805_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                                v___x_3806_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
                                                v___x_3807_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
                                                crate::leanh::lean_inc(v_currMacroScope_3802_);
                                                crate::leanh::lean_inc(v_quotContext_3801_);
                                                v___x_3808_ = l_Lean_addMacroScope(
                                                    v_quotContext_3801_,
                                                    v___x_3807_,
                                                    v_currMacroScope_3802_,
                                                );
                                                v___x_3809_ = crate::leanh::lean_box(0);
                                                v___x_3810_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
                                                crate::leanh::lean_inc(v___x_3804_);
                                                v___x_3811_ =
                                                    crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3811_,
                                                    0,
                                                    v___x_3804_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3811_,
                                                    1,
                                                    v___x_3806_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3811_,
                                                    2,
                                                    v___x_3808_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3811_,
                                                    3,
                                                    v___x_3810_,
                                                );
                                                v___x_3812_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                                v___x_3822_ = l_Lean_TSyntax_getId(v_id_3765_);
                                                crate::leanh::lean_dec(v_id_3765_);
                                                crate::leanh::lean_inc(v___x_3822_);
                                                v___x_3823_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3809_, v___x_3822_);
                                                if crate::leanh::lean_obj_tag(v___x_3823_) == 0 {
                                                    v___x_3824_ = l_Lean_quoteNameMk(v___x_3822_);
                                                    v___y_3814_ = v___x_3824_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_dec(v___x_3822_);
                                                    v_val_3825_ =
                                                        crate::leanh::lean_ctor_get(v___x_3823_, 0);
                                                    crate::leanh::lean_inc(v_val_3825_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_3823_,
                                                        1,
                                                    );
                                                    v___x_3826_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                                    v___x_3827_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                                    v___x_3828_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                                    v___x_3829_ = lean_string_intercalate(
                                                        v___x_3828_,
                                                        v_val_3825_,
                                                    );
                                                    v___x_3830_ = lean_string_append(
                                                        v___x_3827_,
                                                        v___x_3829_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_3829_);
                                                    v___x_3831_ = crate::leanh::lean_box(2);
                                                    v___x_3832_ = l_Lean_Syntax_mkNameLit(
                                                        v___x_3830_,
                                                        v___x_3831_,
                                                    );
                                                    v___x_3833_ = lean_mk_empty_array_with_capacity(
                                                        v___x_3762_,
                                                    );
                                                    v___x_3834_ =
                                                        lean_array_push(v___x_3833_, v___x_3832_);
                                                    v___x_3835_ = crate::leanh::lean_alloc_ctor(
                                                        1,
                                                        3,
                                                        (0) as u32,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3835_,
                                                        0,
                                                        v___x_3831_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3835_,
                                                        1,
                                                        v___x_3826_,
                                                    );
                                                    crate::leanh::lean_ctor_set(
                                                        v___x_3835_,
                                                        2,
                                                        v___x_3834_,
                                                    );
                                                    v___y_3814_ = v___x_3835_;
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___x_3836_ = crate::leanh::lean_unsigned_to_nat(0);
                                    v___x_3837_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v___x_3838_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3837_);
                                    v___x_3839_ =
                                        l_Lean_Syntax_matchesNull(v___x_3838_, v___x_3836_);
                                    if v___x_3839_ == 0 {
                                        crate::leanh::lean_dec(v_x_3741_);
                                        v___x_3840_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                        return v___x_3840_;
                                    } else {
                                        v___x_3841_ = crate::leanh::lean_unsigned_to_nat(1);
                                        v_id_3842_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3841_);
                                        v___x_3843_ = crate::leanh::lean_unsigned_to_nat(3);
                                        v___x_3844_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3843_);
                                        crate::leanh::lean_dec(v_x_3741_);
                                        v___x_3845_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                        crate::leanh::lean_inc(v___x_3844_);
                                        v___x_3846_ =
                                            l_Lean_Syntax_isOfKind(v___x_3844_, v___x_3845_);
                                        if v___x_3846_ == 0 {
                                            v_quotContext_3847_ =
                                                crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                            v_currMacroScope_3848_ =
                                                crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                            v_ref_3849_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                            v___x_3850_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_3849_, v___x_3846_);
                                            v___x_3851_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                            v___x_3852_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
                                            v___x_3853_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
                                            crate::leanh::lean_inc(v_currMacroScope_3848_);
                                            crate::leanh::lean_inc(v_quotContext_3847_);
                                            v___x_3854_ = l_Lean_addMacroScope(
                                                v_quotContext_3847_,
                                                v___x_3853_,
                                                v_currMacroScope_3848_,
                                            );
                                            v___x_3855_ = crate::leanh::lean_box(0);
                                            v___x_3856_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
                                            crate::leanh::lean_inc(v___x_3850_);
                                            v___x_3857_ =
                                                crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3857_,
                                                0,
                                                v___x_3850_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3857_,
                                                1,
                                                v___x_3852_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3857_,
                                                2,
                                                v___x_3854_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3857_,
                                                3,
                                                v___x_3856_,
                                            );
                                            v___x_3858_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                            v___x_3864_ = l_Lean_TSyntax_getId(v_id_3842_);
                                            crate::leanh::lean_dec(v_id_3842_);
                                            crate::leanh::lean_inc(v___x_3864_);
                                            v___x_3865_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3855_, v___x_3864_);
                                            if crate::leanh::lean_obj_tag(v___x_3865_) == 0 {
                                                v___x_3866_ = l_Lean_quoteNameMk(v___x_3864_);
                                                v___y_3860_ = v___x_3866_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_3864_);
                                                v_val_3867_ =
                                                    crate::leanh::lean_ctor_get(v___x_3865_, 0);
                                                crate::leanh::lean_inc(v_val_3867_);
                                                crate::leanh::lean_dec_ref_known(v___x_3865_, 1);
                                                v___x_3868_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                                v___x_3869_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                                v___x_3870_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                                v___x_3871_ = lean_string_intercalate(
                                                    v___x_3870_,
                                                    v_val_3867_,
                                                );
                                                v___x_3872_ =
                                                    lean_string_append(v___x_3869_, v___x_3871_);
                                                crate::leanh::lean_dec_ref(v___x_3871_);
                                                v___x_3873_ = crate::leanh::lean_box(2);
                                                v___x_3874_ = l_Lean_Syntax_mkNameLit(
                                                    v___x_3872_,
                                                    v___x_3873_,
                                                );
                                                v___x_3875_ =
                                                    lean_mk_empty_array_with_capacity(v___x_3841_);
                                                v___x_3876_ =
                                                    lean_array_push(v___x_3875_, v___x_3874_);
                                                v___x_3877_ =
                                                    crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3877_,
                                                    0,
                                                    v___x_3873_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3877_,
                                                    1,
                                                    v___x_3868_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3877_,
                                                    2,
                                                    v___x_3876_,
                                                );
                                                v___y_3860_ = v___x_3877_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            v_quotContext_3878_ =
                                                crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                            v_currMacroScope_3879_ =
                                                crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                            v_ref_3880_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                            v___x_3881_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_3880_, v___x_3751_);
                                            v___x_3882_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                            v___x_3883_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
                                            v___x_3884_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
                                            crate::leanh::lean_inc(v_currMacroScope_3879_);
                                            crate::leanh::lean_inc(v_quotContext_3878_);
                                            v___x_3885_ = l_Lean_addMacroScope(
                                                v_quotContext_3878_,
                                                v___x_3884_,
                                                v_currMacroScope_3879_,
                                            );
                                            v___x_3886_ = crate::leanh::lean_box(0);
                                            v___x_3887_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
                                            crate::leanh::lean_inc(v___x_3881_);
                                            v___x_3888_ =
                                                crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3888_,
                                                0,
                                                v___x_3881_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3888_,
                                                1,
                                                v___x_3883_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3888_,
                                                2,
                                                v___x_3885_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3888_,
                                                3,
                                                v___x_3887_,
                                            );
                                            v___x_3889_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                            v___x_3899_ = l_Lean_TSyntax_getId(v_id_3842_);
                                            crate::leanh::lean_dec(v_id_3842_);
                                            crate::leanh::lean_inc(v___x_3899_);
                                            v___x_3900_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3886_, v___x_3899_);
                                            if crate::leanh::lean_obj_tag(v___x_3900_) == 0 {
                                                v___x_3901_ = l_Lean_quoteNameMk(v___x_3899_);
                                                v___y_3891_ = v___x_3901_;
                                                state = 4;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_3899_);
                                                v_val_3902_ =
                                                    crate::leanh::lean_ctor_get(v___x_3900_, 0);
                                                crate::leanh::lean_inc(v_val_3902_);
                                                crate::leanh::lean_dec_ref_known(v___x_3900_, 1);
                                                v___x_3903_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                                v___x_3904_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                                v___x_3905_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                                v___x_3906_ = lean_string_intercalate(
                                                    v___x_3905_,
                                                    v_val_3902_,
                                                );
                                                v___x_3907_ =
                                                    lean_string_append(v___x_3904_, v___x_3906_);
                                                crate::leanh::lean_dec_ref(v___x_3906_);
                                                v___x_3908_ = crate::leanh::lean_box(2);
                                                v___x_3909_ = l_Lean_Syntax_mkNameLit(
                                                    v___x_3907_,
                                                    v___x_3908_,
                                                );
                                                v___x_3910_ =
                                                    lean_mk_empty_array_with_capacity(v___x_3841_);
                                                v___x_3911_ =
                                                    lean_array_push(v___x_3910_, v___x_3909_);
                                                v___x_3912_ =
                                                    crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3912_,
                                                    0,
                                                    v___x_3908_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3912_,
                                                    1,
                                                    v___x_3903_,
                                                );
                                                crate::leanh::lean_ctor_set(
                                                    v___x_3912_,
                                                    2,
                                                    v___x_3911_,
                                                );
                                                v___y_3891_ = v___x_3912_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_3913_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_3914_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3915_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3914_);
                                v___x_3916_ = l_Lean_Syntax_matchesNull(v___x_3915_, v___x_3913_);
                                if v___x_3916_ == 0 {
                                    crate::leanh::lean_dec(v_x_3741_);
                                    v___x_3917_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                    return v___x_3917_;
                                } else {
                                    v___x_3918_ = crate::leanh::lean_unsigned_to_nat(1);
                                    v___x_3919_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3918_);
                                    v___x_3920_ = crate::leanh::lean_unsigned_to_nat(2);
                                    v_id_3921_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3920_);
                                    v___x_3922_ = crate::leanh::lean_unsigned_to_nat(4);
                                    v___x_3923_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3922_);
                                    crate::leanh::lean_dec(v_x_3741_);
                                    v___x_3924_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                    crate::leanh::lean_inc(v___x_3923_);
                                    v___x_3925_ = l_Lean_Syntax_isOfKind(v___x_3923_, v___x_3924_);
                                    if v___x_3925_ == 0 {
                                        v_quotContext_3926_ =
                                            crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                        v_currMacroScope_3927_ =
                                            crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                        v_ref_3928_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                        v___x_3929_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_3928_, v___x_3925_);
                                        v___x_3930_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                        v___x_3931_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
                                        v___x_3932_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
                                        crate::leanh::lean_inc(v_currMacroScope_3927_);
                                        crate::leanh::lean_inc(v_quotContext_3926_);
                                        v___x_3933_ = l_Lean_addMacroScope(
                                            v_quotContext_3926_,
                                            v___x_3932_,
                                            v_currMacroScope_3927_,
                                        );
                                        v___x_3934_ = crate::leanh::lean_box(0);
                                        v___x_3935_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
                                        crate::leanh::lean_inc(v___x_3929_);
                                        v___x_3936_ =
                                            crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3936_, 0, v___x_3929_);
                                        crate::leanh::lean_ctor_set(v___x_3936_, 1, v___x_3931_);
                                        crate::leanh::lean_ctor_set(v___x_3936_, 2, v___x_3933_);
                                        crate::leanh::lean_ctor_set(v___x_3936_, 3, v___x_3935_);
                                        v___x_3937_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                        v___x_3943_ = l_Lean_TSyntax_getId(v_id_3921_);
                                        crate::leanh::lean_dec(v_id_3921_);
                                        crate::leanh::lean_inc(v___x_3943_);
                                        v___x_3944_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3934_, v___x_3943_);
                                        if crate::leanh::lean_obj_tag(v___x_3944_) == 0 {
                                            v___x_3945_ = l_Lean_quoteNameMk(v___x_3943_);
                                            v___y_3939_ = v___x_3945_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_3943_);
                                            v_val_3946_ =
                                                crate::leanh::lean_ctor_get(v___x_3944_, 0);
                                            crate::leanh::lean_inc(v_val_3946_);
                                            crate::leanh::lean_dec_ref_known(v___x_3944_, 1);
                                            v___x_3947_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                            v___x_3948_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                            v___x_3949_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                            v___x_3950_ =
                                                lean_string_intercalate(v___x_3949_, v_val_3946_);
                                            v___x_3951_ =
                                                lean_string_append(v___x_3948_, v___x_3950_);
                                            crate::leanh::lean_dec_ref(v___x_3950_);
                                            v___x_3952_ = crate::leanh::lean_box(2);
                                            v___x_3953_ =
                                                l_Lean_Syntax_mkNameLit(v___x_3951_, v___x_3952_);
                                            v___x_3954_ =
                                                lean_mk_empty_array_with_capacity(v___x_3918_);
                                            v___x_3955_ = lean_array_push(v___x_3954_, v___x_3953_);
                                            v___x_3956_ =
                                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3956_,
                                                0,
                                                v___x_3952_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3956_,
                                                1,
                                                v___x_3947_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3956_,
                                                2,
                                                v___x_3955_,
                                            );
                                            v___y_3939_ = v___x_3956_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        v_quotContext_3957_ =
                                            crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                        v_currMacroScope_3958_ =
                                            crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                        v_ref_3959_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                        v___x_3960_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_3959_, v___x_3749_);
                                        v___x_3961_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                        v___x_3962_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
                                        v___x_3963_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
                                        crate::leanh::lean_inc(v_currMacroScope_3958_);
                                        crate::leanh::lean_inc(v_quotContext_3957_);
                                        v___x_3964_ = l_Lean_addMacroScope(
                                            v_quotContext_3957_,
                                            v___x_3963_,
                                            v_currMacroScope_3958_,
                                        );
                                        v___x_3965_ = crate::leanh::lean_box(0);
                                        v___x_3966_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
                                        crate::leanh::lean_inc(v___x_3960_);
                                        v___x_3967_ =
                                            crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_3967_, 0, v___x_3960_);
                                        crate::leanh::lean_ctor_set(v___x_3967_, 1, v___x_3962_);
                                        crate::leanh::lean_ctor_set(v___x_3967_, 2, v___x_3964_);
                                        crate::leanh::lean_ctor_set(v___x_3967_, 3, v___x_3966_);
                                        v___x_3968_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                        v___x_3978_ = l_Lean_TSyntax_getId(v_id_3921_);
                                        crate::leanh::lean_dec(v_id_3921_);
                                        crate::leanh::lean_inc(v___x_3978_);
                                        v___x_3979_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3965_, v___x_3978_);
                                        if crate::leanh::lean_obj_tag(v___x_3979_) == 0 {
                                            v___x_3980_ = l_Lean_quoteNameMk(v___x_3978_);
                                            v___y_3970_ = v___x_3980_;
                                            state = 6;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_3978_);
                                            v_val_3981_ =
                                                crate::leanh::lean_ctor_get(v___x_3979_, 0);
                                            crate::leanh::lean_inc(v_val_3981_);
                                            crate::leanh::lean_dec_ref_known(v___x_3979_, 1);
                                            v___x_3982_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                            v___x_3983_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                            v___x_3984_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                            v___x_3985_ =
                                                lean_string_intercalate(v___x_3984_, v_val_3981_);
                                            v___x_3986_ =
                                                lean_string_append(v___x_3983_, v___x_3985_);
                                            crate::leanh::lean_dec_ref(v___x_3985_);
                                            v___x_3987_ = crate::leanh::lean_box(2);
                                            v___x_3988_ =
                                                l_Lean_Syntax_mkNameLit(v___x_3986_, v___x_3987_);
                                            v___x_3989_ =
                                                lean_mk_empty_array_with_capacity(v___x_3918_);
                                            v___x_3990_ = lean_array_push(v___x_3989_, v___x_3988_);
                                            v___x_3991_ =
                                                crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3991_,
                                                0,
                                                v___x_3987_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3991_,
                                                1,
                                                v___x_3982_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_3991_,
                                                2,
                                                v___x_3990_,
                                            );
                                            v___y_3970_ = v___x_3991_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_3992_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_3993_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_3994_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3993_);
                            v___x_3995_ = l_Lean_Syntax_matchesNull(v___x_3994_, v___x_3992_);
                            if v___x_3995_ == 0 {
                                crate::leanh::lean_dec(v_x_3741_);
                                v___x_3996_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                return v___x_3996_;
                            } else {
                                v___x_3997_ = crate::leanh::lean_unsigned_to_nat(1);
                                v_id_3998_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3997_);
                                v___x_3999_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_4000_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3999_);
                                crate::leanh::lean_dec(v_x_3741_);
                                v___x_4001_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                crate::leanh::lean_inc(v___x_4000_);
                                v___x_4002_ = l_Lean_Syntax_isOfKind(v___x_4000_, v___x_4001_);
                                if v___x_4002_ == 0 {
                                    v_quotContext_4003_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                    v_currMacroScope_4004_ =
                                        crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                    v_ref_4005_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                    v___x_4006_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4005_, v___x_4002_);
                                    v___x_4007_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                    v___x_4008_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
                                    v___x_4009_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
                                    crate::leanh::lean_inc(v_currMacroScope_4004_);
                                    crate::leanh::lean_inc(v_quotContext_4003_);
                                    v___x_4010_ = l_Lean_addMacroScope(
                                        v_quotContext_4003_,
                                        v___x_4009_,
                                        v_currMacroScope_4004_,
                                    );
                                    v___x_4011_ = crate::leanh::lean_box(0);
                                    v___x_4012_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
                                    crate::leanh::lean_inc(v___x_4006_);
                                    v___x_4013_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4013_, 0, v___x_4006_);
                                    crate::leanh::lean_ctor_set(v___x_4013_, 1, v___x_4008_);
                                    crate::leanh::lean_ctor_set(v___x_4013_, 2, v___x_4010_);
                                    crate::leanh::lean_ctor_set(v___x_4013_, 3, v___x_4012_);
                                    v___x_4014_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                    v___x_4020_ = l_Lean_TSyntax_getId(v_id_3998_);
                                    crate::leanh::lean_dec(v_id_3998_);
                                    crate::leanh::lean_inc(v___x_4020_);
                                    v___x_4021_ =
                                        l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                            v___x_4011_,
                                            v___x_4020_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_4021_) == 0 {
                                        v___x_4022_ = l_Lean_quoteNameMk(v___x_4020_);
                                        v___y_4016_ = v___x_4022_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4020_);
                                        v_val_4023_ = crate::leanh::lean_ctor_get(v___x_4021_, 0);
                                        crate::leanh::lean_inc(v_val_4023_);
                                        crate::leanh::lean_dec_ref_known(v___x_4021_, 1);
                                        v___x_4024_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                        v___x_4025_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                        v___x_4026_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                        v___x_4027_ =
                                            lean_string_intercalate(v___x_4026_, v_val_4023_);
                                        v___x_4028_ = lean_string_append(v___x_4025_, v___x_4027_);
                                        crate::leanh::lean_dec_ref(v___x_4027_);
                                        v___x_4029_ = crate::leanh::lean_box(2);
                                        v___x_4030_ =
                                            l_Lean_Syntax_mkNameLit(v___x_4028_, v___x_4029_);
                                        v___x_4031_ =
                                            lean_mk_empty_array_with_capacity(v___x_3997_);
                                        v___x_4032_ = lean_array_push(v___x_4031_, v___x_4030_);
                                        v___x_4033_ =
                                            crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4033_, 0, v___x_4029_);
                                        crate::leanh::lean_ctor_set(v___x_4033_, 1, v___x_4024_);
                                        crate::leanh::lean_ctor_set(v___x_4033_, 2, v___x_4032_);
                                        v___y_4016_ = v___x_4033_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    v_quotContext_4034_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                    v_currMacroScope_4035_ =
                                        crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                    v_ref_4036_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                    v___x_4037_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4036_, v___x_3747_);
                                    v___x_4038_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                    v___x_4039_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
                                    v___x_4040_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
                                    crate::leanh::lean_inc(v_currMacroScope_4035_);
                                    crate::leanh::lean_inc(v_quotContext_4034_);
                                    v___x_4041_ = l_Lean_addMacroScope(
                                        v_quotContext_4034_,
                                        v___x_4040_,
                                        v_currMacroScope_4035_,
                                    );
                                    v___x_4042_ = crate::leanh::lean_box(0);
                                    v___x_4043_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
                                    crate::leanh::lean_inc(v___x_4037_);
                                    v___x_4044_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4037_);
                                    crate::leanh::lean_ctor_set(v___x_4044_, 1, v___x_4039_);
                                    crate::leanh::lean_ctor_set(v___x_4044_, 2, v___x_4041_);
                                    crate::leanh::lean_ctor_set(v___x_4044_, 3, v___x_4043_);
                                    v___x_4045_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                    v___x_4055_ = l_Lean_TSyntax_getId(v_id_3998_);
                                    crate::leanh::lean_dec(v_id_3998_);
                                    crate::leanh::lean_inc(v___x_4055_);
                                    v___x_4056_ =
                                        l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                            v___x_4042_,
                                            v___x_4055_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_4056_) == 0 {
                                        v___x_4057_ = l_Lean_quoteNameMk(v___x_4055_);
                                        v___y_4047_ = v___x_4057_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4055_);
                                        v_val_4058_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                                        crate::leanh::lean_inc(v_val_4058_);
                                        crate::leanh::lean_dec_ref_known(v___x_4056_, 1);
                                        v___x_4059_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                        v___x_4060_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                        v___x_4061_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                        v___x_4062_ =
                                            lean_string_intercalate(v___x_4061_, v_val_4058_);
                                        v___x_4063_ = lean_string_append(v___x_4060_, v___x_4062_);
                                        crate::leanh::lean_dec_ref(v___x_4062_);
                                        v___x_4064_ = crate::leanh::lean_box(2);
                                        v___x_4065_ =
                                            l_Lean_Syntax_mkNameLit(v___x_4063_, v___x_4064_);
                                        v___x_4066_ =
                                            lean_mk_empty_array_with_capacity(v___x_3997_);
                                        v___x_4067_ = lean_array_push(v___x_4066_, v___x_4065_);
                                        v___x_4068_ =
                                            crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_4068_, 0, v___x_4064_);
                                        crate::leanh::lean_ctor_set(v___x_4068_, 1, v___x_4059_);
                                        crate::leanh::lean_ctor_set(v___x_4068_, 2, v___x_4067_);
                                        v___y_4047_ = v___x_4068_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_4069_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_4070_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_4071_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4070_);
                        v___x_4072_ = l_Lean_Syntax_matchesNull(v___x_4071_, v___x_4069_);
                        if v___x_4072_ == 0 {
                            crate::leanh::lean_dec(v_x_3741_);
                            v___x_4073_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                            return v___x_4073_;
                        } else {
                            v___x_4074_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4075_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4074_);
                            v___x_4076_ = crate::leanh::lean_unsigned_to_nat(2);
                            v_id_4077_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4076_);
                            v___x_4078_ = crate::leanh::lean_unsigned_to_nat(4);
                            v___x_4079_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4078_);
                            crate::leanh::lean_dec(v_x_3741_);
                            v___x_4080_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                            crate::leanh::lean_inc(v___x_4079_);
                            v___x_4081_ = l_Lean_Syntax_isOfKind(v___x_4079_, v___x_4080_);
                            if v___x_4081_ == 0 {
                                v_quotContext_4082_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4083_ = crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                v_ref_4084_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                v___x_4085_ = l_Lean_SourceInfo_fromRef(v_ref_4084_, v___x_4081_);
                                v___x_4086_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4087_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
                                v___x_4088_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
                                crate::leanh::lean_inc(v_currMacroScope_4083_);
                                crate::leanh::lean_inc(v_quotContext_4082_);
                                v___x_4089_ = l_Lean_addMacroScope(
                                    v_quotContext_4082_,
                                    v___x_4088_,
                                    v_currMacroScope_4083_,
                                );
                                v___x_4090_ = crate::leanh::lean_box(0);
                                v___x_4091_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
                                crate::leanh::lean_inc(v___x_4085_);
                                v___x_4092_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4092_, 0, v___x_4085_);
                                crate::leanh::lean_ctor_set(v___x_4092_, 1, v___x_4087_);
                                crate::leanh::lean_ctor_set(v___x_4092_, 2, v___x_4089_);
                                crate::leanh::lean_ctor_set(v___x_4092_, 3, v___x_4091_);
                                v___x_4093_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4099_ = l_Lean_TSyntax_getId(v_id_4077_);
                                crate::leanh::lean_dec(v_id_4077_);
                                crate::leanh::lean_inc(v___x_4099_);
                                v___x_4100_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4090_,
                                        v___x_4099_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_4100_) == 0 {
                                    v___x_4101_ = l_Lean_quoteNameMk(v___x_4099_);
                                    v___y_4095_ = v___x_4101_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4099_);
                                    v_val_4102_ = crate::leanh::lean_ctor_get(v___x_4100_, 0);
                                    crate::leanh::lean_inc(v_val_4102_);
                                    crate::leanh::lean_dec_ref_known(v___x_4100_, 1);
                                    v___x_4103_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4104_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4105_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4106_ = lean_string_intercalate(v___x_4105_, v_val_4102_);
                                    v___x_4107_ = lean_string_append(v___x_4104_, v___x_4106_);
                                    crate::leanh::lean_dec_ref(v___x_4106_);
                                    v___x_4108_ = crate::leanh::lean_box(2);
                                    v___x_4109_ = l_Lean_Syntax_mkNameLit(v___x_4107_, v___x_4108_);
                                    v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4074_);
                                    v___x_4111_ = lean_array_push(v___x_4110_, v___x_4109_);
                                    v___x_4112_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4112_, 0, v___x_4108_);
                                    crate::leanh::lean_ctor_set(v___x_4112_, 1, v___x_4103_);
                                    crate::leanh::lean_ctor_set(v___x_4112_, 2, v___x_4111_);
                                    v___y_4095_ = v___x_4112_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v_quotContext_4113_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4114_ = crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                v_ref_4115_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                v___x_4116_ = l_Lean_SourceInfo_fromRef(v_ref_4115_, v___x_3745_);
                                v___x_4117_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4118_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
                                v___x_4119_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
                                crate::leanh::lean_inc(v_currMacroScope_4114_);
                                crate::leanh::lean_inc(v_quotContext_4113_);
                                v___x_4120_ = l_Lean_addMacroScope(
                                    v_quotContext_4113_,
                                    v___x_4119_,
                                    v_currMacroScope_4114_,
                                );
                                v___x_4121_ = crate::leanh::lean_box(0);
                                v___x_4122_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
                                crate::leanh::lean_inc(v___x_4116_);
                                v___x_4123_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4123_, 0, v___x_4116_);
                                crate::leanh::lean_ctor_set(v___x_4123_, 1, v___x_4118_);
                                crate::leanh::lean_ctor_set(v___x_4123_, 2, v___x_4120_);
                                crate::leanh::lean_ctor_set(v___x_4123_, 3, v___x_4122_);
                                v___x_4124_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4134_ = l_Lean_TSyntax_getId(v_id_4077_);
                                crate::leanh::lean_dec(v_id_4077_);
                                crate::leanh::lean_inc(v___x_4134_);
                                v___x_4135_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4121_,
                                        v___x_4134_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_4135_) == 0 {
                                    v___x_4136_ = l_Lean_quoteNameMk(v___x_4134_);
                                    v___y_4126_ = v___x_4136_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4134_);
                                    v_val_4137_ = crate::leanh::lean_ctor_get(v___x_4135_, 0);
                                    crate::leanh::lean_inc(v_val_4137_);
                                    crate::leanh::lean_dec_ref_known(v___x_4135_, 1);
                                    v___x_4138_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4139_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4140_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4141_ = lean_string_intercalate(v___x_4140_, v_val_4137_);
                                    v___x_4142_ = lean_string_append(v___x_4139_, v___x_4141_);
                                    crate::leanh::lean_dec_ref(v___x_4141_);
                                    v___x_4143_ = crate::leanh::lean_box(2);
                                    v___x_4144_ = l_Lean_Syntax_mkNameLit(v___x_4142_, v___x_4143_);
                                    v___x_4145_ = lean_mk_empty_array_with_capacity(v___x_4074_);
                                    v___x_4146_ = lean_array_push(v___x_4145_, v___x_4144_);
                                    v___x_4147_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4147_, 0, v___x_4143_);
                                    crate::leanh::lean_ctor_set(v___x_4147_, 1, v___x_4138_);
                                    crate::leanh::lean_ctor_set(v___x_4147_, 2, v___x_4146_);
                                    v___y_4126_ = v___x_4147_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_4148_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4149_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_id_4150_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4149_);
                    v___x_4151_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
                    crate::leanh::lean_inc(v_id_4150_);
                    v___x_4152_ = l_Lean_Syntax_isOfKind(v_id_4150_, v___x_4151_);
                    if v___x_4152_ == 0 {
                        v___x_4153_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_4154_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4153_);
                        v___x_4155_ = l_Lean_Syntax_matchesNull(v___x_4154_, v___x_4148_);
                        if v___x_4155_ == 0 {
                            crate::leanh::lean_dec(v_id_4150_);
                            crate::leanh::lean_dec(v_x_3741_);
                            v___x_4156_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                            return v___x_4156_;
                        } else {
                            v_quotContext_4157_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                            v_currMacroScope_4158_ = crate::leanh::lean_ctor_get(v_a_3742_, 2);
                            v_ref_4159_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                            v___x_4160_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4161_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4160_);
                            crate::leanh::lean_dec(v_x_3741_);
                            v___x_4162_ = l_Lean_SourceInfo_fromRef(v_ref_4159_, v___x_4152_);
                            v___x_4163_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                            v___x_4164_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
                            v___x_4165_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
                            crate::leanh::lean_inc(v_currMacroScope_4158_);
                            crate::leanh::lean_inc(v_quotContext_4157_);
                            v___x_4166_ = l_Lean_addMacroScope(
                                v_quotContext_4157_,
                                v___x_4165_,
                                v_currMacroScope_4158_,
                            );
                            v___x_4167_ = crate::leanh::lean_box(0);
                            v___x_4168_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
                            crate::leanh::lean_inc(v___x_4162_);
                            v___x_4169_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4169_, 0, v___x_4162_);
                            crate::leanh::lean_ctor_set(v___x_4169_, 1, v___x_4164_);
                            crate::leanh::lean_ctor_set(v___x_4169_, 2, v___x_4166_);
                            crate::leanh::lean_ctor_set(v___x_4169_, 3, v___x_4168_);
                            v___x_4170_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                            v___x_4176_ = l_Lean_TSyntax_getId(v_id_4150_);
                            crate::leanh::lean_dec(v_id_4150_);
                            crate::leanh::lean_inc(v___x_4176_);
                            v___x_4177_ =
                                l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                    v___x_4167_,
                                    v___x_4176_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_4177_) == 0 {
                                v___x_4178_ = l_Lean_quoteNameMk(v___x_4176_);
                                v___y_4172_ = v___x_4178_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4176_);
                                v_val_4179_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                                crate::leanh::lean_inc(v_val_4179_);
                                crate::leanh::lean_dec_ref_known(v___x_4177_, 1);
                                v___x_4180_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                v___x_4181_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                v___x_4182_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                v___x_4183_ = lean_string_intercalate(v___x_4182_, v_val_4179_);
                                v___x_4184_ = lean_string_append(v___x_4181_, v___x_4183_);
                                crate::leanh::lean_dec_ref(v___x_4183_);
                                v___x_4185_ = crate::leanh::lean_box(2);
                                v___x_4186_ = l_Lean_Syntax_mkNameLit(v___x_4184_, v___x_4185_);
                                v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4149_);
                                v___x_4188_ = lean_array_push(v___x_4187_, v___x_4186_);
                                v___x_4189_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4189_, 0, v___x_4185_);
                                crate::leanh::lean_ctor_set(v___x_4189_, 1, v___x_4180_);
                                crate::leanh::lean_ctor_set(v___x_4189_, 2, v___x_4188_);
                                v___y_4172_ = v___x_4189_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_4190_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_4191_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4190_);
                        v___x_4192_ = l_Lean_Syntax_matchesNull(v___x_4191_, v___x_4148_);
                        if v___x_4192_ == 0 {
                            crate::leanh::lean_dec(v_id_4150_);
                            crate::leanh::lean_dec(v_x_3741_);
                            v___x_4193_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                            return v___x_4193_;
                        } else {
                            v___x_4194_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4195_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4194_);
                            crate::leanh::lean_dec(v_x_3741_);
                            v___x_4196_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                            crate::leanh::lean_inc(v___x_4195_);
                            v___x_4197_ = l_Lean_Syntax_isOfKind(v___x_4195_, v___x_4196_);
                            if v___x_4197_ == 0 {
                                v_quotContext_4198_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4199_ = crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                v_ref_4200_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                v___x_4201_ = l_Lean_SourceInfo_fromRef(v_ref_4200_, v___x_4197_);
                                v___x_4202_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4203_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
                                v___x_4204_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
                                crate::leanh::lean_inc(v_currMacroScope_4199_);
                                crate::leanh::lean_inc(v_quotContext_4198_);
                                v___x_4205_ = l_Lean_addMacroScope(
                                    v_quotContext_4198_,
                                    v___x_4204_,
                                    v_currMacroScope_4199_,
                                );
                                v___x_4206_ = crate::leanh::lean_box(0);
                                v___x_4207_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
                                crate::leanh::lean_inc(v___x_4201_);
                                v___x_4208_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4208_, 0, v___x_4201_);
                                crate::leanh::lean_ctor_set(v___x_4208_, 1, v___x_4203_);
                                crate::leanh::lean_ctor_set(v___x_4208_, 2, v___x_4205_);
                                crate::leanh::lean_ctor_set(v___x_4208_, 3, v___x_4207_);
                                v___x_4209_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4215_ = l_Lean_TSyntax_getId(v_id_4150_);
                                crate::leanh::lean_dec(v_id_4150_);
                                crate::leanh::lean_inc(v___x_4215_);
                                v___x_4216_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4206_,
                                        v___x_4215_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_4216_) == 0 {
                                    v___x_4217_ = l_Lean_quoteNameMk(v___x_4215_);
                                    v___y_4211_ = v___x_4217_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4215_);
                                    v_val_4218_ = crate::leanh::lean_ctor_get(v___x_4216_, 0);
                                    crate::leanh::lean_inc(v_val_4218_);
                                    crate::leanh::lean_dec_ref_known(v___x_4216_, 1);
                                    v___x_4219_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4220_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4221_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4222_ = lean_string_intercalate(v___x_4221_, v_val_4218_);
                                    v___x_4223_ = lean_string_append(v___x_4220_, v___x_4222_);
                                    crate::leanh::lean_dec_ref(v___x_4222_);
                                    v___x_4224_ = crate::leanh::lean_box(2);
                                    v___x_4225_ = l_Lean_Syntax_mkNameLit(v___x_4223_, v___x_4224_);
                                    v___x_4226_ = lean_mk_empty_array_with_capacity(v___x_4149_);
                                    v___x_4227_ = lean_array_push(v___x_4226_, v___x_4225_);
                                    v___x_4228_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4228_, 0, v___x_4224_);
                                    crate::leanh::lean_ctor_set(v___x_4228_, 1, v___x_4219_);
                                    crate::leanh::lean_ctor_set(v___x_4228_, 2, v___x_4227_);
                                    v___y_4211_ = v___x_4228_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                v_quotContext_4229_ = crate::leanh::lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4230_ = crate::leanh::lean_ctor_get(v_a_3742_, 2);
                                v_ref_4231_ = crate::leanh::lean_ctor_get(v_a_3742_, 5);
                                v___x_4232_ = 0;
                                v___x_4233_ = l_Lean_SourceInfo_fromRef(v_ref_4231_, v___x_4232_);
                                v___x_4234_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4235_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
                                v___x_4236_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
                                crate::leanh::lean_inc(v_currMacroScope_4230_);
                                crate::leanh::lean_inc(v_quotContext_4229_);
                                v___x_4237_ = l_Lean_addMacroScope(
                                    v_quotContext_4229_,
                                    v___x_4236_,
                                    v_currMacroScope_4230_,
                                );
                                v___x_4238_ = crate::leanh::lean_box(0);
                                v___x_4239_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
                                crate::leanh::lean_inc(v___x_4233_);
                                v___x_4240_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_4240_, 0, v___x_4233_);
                                crate::leanh::lean_ctor_set(v___x_4240_, 1, v___x_4235_);
                                crate::leanh::lean_ctor_set(v___x_4240_, 2, v___x_4237_);
                                crate::leanh::lean_ctor_set(v___x_4240_, 3, v___x_4239_);
                                v___x_4241_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4251_ = l_Lean_TSyntax_getId(v_id_4150_);
                                crate::leanh::lean_dec(v_id_4150_);
                                crate::leanh::lean_inc(v___x_4251_);
                                v___x_4252_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4238_,
                                        v___x_4251_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_4252_) == 0 {
                                    v___x_4253_ = l_Lean_quoteNameMk(v___x_4251_);
                                    v___y_4243_ = v___x_4253_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_4251_);
                                    v_val_4254_ = crate::leanh::lean_ctor_get(v___x_4252_, 0);
                                    crate::leanh::lean_inc(v_val_4254_);
                                    crate::leanh::lean_dec_ref_known(v___x_4252_, 1);
                                    v___x_4255_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4256_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4257_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4258_ = lean_string_intercalate(v___x_4257_, v_val_4254_);
                                    v___x_4259_ = lean_string_append(v___x_4256_, v___x_4258_);
                                    crate::leanh::lean_dec_ref(v___x_4258_);
                                    v___x_4260_ = crate::leanh::lean_box(2);
                                    v___x_4261_ = l_Lean_Syntax_mkNameLit(v___x_4259_, v___x_4260_);
                                    v___x_4262_ = lean_mk_empty_array_with_capacity(v___x_4149_);
                                    v___x_4263_ = lean_array_push(v___x_4262_, v___x_4261_);
                                    v___x_4264_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4264_, 0, v___x_4260_);
                                    crate::leanh::lean_ctor_set(v___x_4264_, 1, v___x_4255_);
                                    crate::leanh::lean_ctor_set(v___x_4264_, 2, v___x_4263_);
                                    v___y_4243_ = v___x_4264_;
                                    state = 13;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v___x_3773_);
                v___x_3784_ = l_Lean_Syntax_node3(
                    v___x_3773_,
                    v___x_3781_,
                    v___x_3763_,
                    v___y_3783_,
                    v___x_3767_,
                );
                v___x_3785_ =
                    l_Lean_Syntax_node2(v___x_3773_, v___x_3774_, v___x_3780_, v___x_3784_);
                v___x_3786_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3786_, 0, v___x_3785_);
                crate::leanh::lean_ctor_set(v___x_3786_, 1, v_a_3743_);
                return v___x_3786_;
            }
            2 => {
                v___x_3815_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_3816_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                crate::leanh::lean_inc_n(v___x_3804_, 3);
                v___x_3817_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3817_, 0, v___x_3804_);
                crate::leanh::lean_ctor_set(v___x_3817_, 1, v___x_3816_);
                v___x_3818_ =
                    l_Lean_Syntax_node2(v___x_3804_, v___x_3815_, v___x_3817_, v___x_3767_);
                v___x_3819_ = l_Lean_Syntax_node3(
                    v___x_3804_,
                    v___x_3812_,
                    v___x_3763_,
                    v___y_3814_,
                    v___x_3818_,
                );
                v___x_3820_ =
                    l_Lean_Syntax_node2(v___x_3804_, v___x_3805_, v___x_3811_, v___x_3819_);
                v___x_3821_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3821_, 0, v___x_3820_);
                crate::leanh::lean_ctor_set(v___x_3821_, 1, v_a_3743_);
                return v___x_3821_;
            }
            3 => {
                crate::leanh::lean_inc(v___x_3850_);
                v___x_3861_ =
                    l_Lean_Syntax_node2(v___x_3850_, v___x_3858_, v___y_3860_, v___x_3844_);
                v___x_3862_ =
                    l_Lean_Syntax_node2(v___x_3850_, v___x_3851_, v___x_3857_, v___x_3861_);
                v___x_3863_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3863_, 0, v___x_3862_);
                crate::leanh::lean_ctor_set(v___x_3863_, 1, v_a_3743_);
                return v___x_3863_;
            }
            4 => {
                v___x_3892_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_3893_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                crate::leanh::lean_inc_n(v___x_3881_, 3);
                v___x_3894_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3894_, 0, v___x_3881_);
                crate::leanh::lean_ctor_set(v___x_3894_, 1, v___x_3893_);
                v___x_3895_ =
                    l_Lean_Syntax_node2(v___x_3881_, v___x_3892_, v___x_3894_, v___x_3844_);
                v___x_3896_ =
                    l_Lean_Syntax_node2(v___x_3881_, v___x_3889_, v___y_3891_, v___x_3895_);
                v___x_3897_ =
                    l_Lean_Syntax_node2(v___x_3881_, v___x_3882_, v___x_3888_, v___x_3896_);
                v___x_3898_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                crate::leanh::lean_ctor_set(v___x_3898_, 1, v_a_3743_);
                return v___x_3898_;
            }
            5 => {
                crate::leanh::lean_inc(v___x_3929_);
                v___x_3940_ = l_Lean_Syntax_node3(
                    v___x_3929_,
                    v___x_3937_,
                    v___x_3919_,
                    v___y_3939_,
                    v___x_3923_,
                );
                v___x_3941_ =
                    l_Lean_Syntax_node2(v___x_3929_, v___x_3930_, v___x_3936_, v___x_3940_);
                v___x_3942_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3942_, 0, v___x_3941_);
                crate::leanh::lean_ctor_set(v___x_3942_, 1, v_a_3743_);
                return v___x_3942_;
            }
            6 => {
                v___x_3971_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_3972_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                crate::leanh::lean_inc_n(v___x_3960_, 3);
                v___x_3973_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3973_, 0, v___x_3960_);
                crate::leanh::lean_ctor_set(v___x_3973_, 1, v___x_3972_);
                v___x_3974_ =
                    l_Lean_Syntax_node2(v___x_3960_, v___x_3971_, v___x_3973_, v___x_3923_);
                v___x_3975_ = l_Lean_Syntax_node3(
                    v___x_3960_,
                    v___x_3968_,
                    v___x_3919_,
                    v___y_3970_,
                    v___x_3974_,
                );
                v___x_3976_ =
                    l_Lean_Syntax_node2(v___x_3960_, v___x_3961_, v___x_3967_, v___x_3975_);
                v___x_3977_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3977_, 0, v___x_3976_);
                crate::leanh::lean_ctor_set(v___x_3977_, 1, v_a_3743_);
                return v___x_3977_;
            }
            7 => {
                crate::leanh::lean_inc(v___x_4006_);
                v___x_4017_ =
                    l_Lean_Syntax_node2(v___x_4006_, v___x_4014_, v___y_4016_, v___x_4000_);
                v___x_4018_ =
                    l_Lean_Syntax_node2(v___x_4006_, v___x_4007_, v___x_4013_, v___x_4017_);
                v___x_4019_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4019_, 0, v___x_4018_);
                crate::leanh::lean_ctor_set(v___x_4019_, 1, v_a_3743_);
                return v___x_4019_;
            }
            8 => {
                v___x_4048_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_4049_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                crate::leanh::lean_inc_n(v___x_4037_, 3);
                v___x_4050_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4050_, 0, v___x_4037_);
                crate::leanh::lean_ctor_set(v___x_4050_, 1, v___x_4049_);
                v___x_4051_ =
                    l_Lean_Syntax_node2(v___x_4037_, v___x_4048_, v___x_4050_, v___x_4000_);
                v___x_4052_ =
                    l_Lean_Syntax_node2(v___x_4037_, v___x_4045_, v___y_4047_, v___x_4051_);
                v___x_4053_ =
                    l_Lean_Syntax_node2(v___x_4037_, v___x_4038_, v___x_4044_, v___x_4052_);
                v___x_4054_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4054_, 0, v___x_4053_);
                crate::leanh::lean_ctor_set(v___x_4054_, 1, v_a_3743_);
                return v___x_4054_;
            }
            9 => {
                crate::leanh::lean_inc(v___x_4085_);
                v___x_4096_ = l_Lean_Syntax_node3(
                    v___x_4085_,
                    v___x_4093_,
                    v___x_4075_,
                    v___y_4095_,
                    v___x_4079_,
                );
                v___x_4097_ =
                    l_Lean_Syntax_node2(v___x_4085_, v___x_4086_, v___x_4092_, v___x_4096_);
                v___x_4098_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4098_, 0, v___x_4097_);
                crate::leanh::lean_ctor_set(v___x_4098_, 1, v_a_3743_);
                return v___x_4098_;
            }
            10 => {
                v___x_4127_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_4128_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                crate::leanh::lean_inc_n(v___x_4116_, 3);
                v___x_4129_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4129_, 0, v___x_4116_);
                crate::leanh::lean_ctor_set(v___x_4129_, 1, v___x_4128_);
                v___x_4130_ =
                    l_Lean_Syntax_node2(v___x_4116_, v___x_4127_, v___x_4129_, v___x_4079_);
                v___x_4131_ = l_Lean_Syntax_node3(
                    v___x_4116_,
                    v___x_4124_,
                    v___x_4075_,
                    v___y_4126_,
                    v___x_4130_,
                );
                v___x_4132_ =
                    l_Lean_Syntax_node2(v___x_4116_, v___x_4117_, v___x_4123_, v___x_4131_);
                v___x_4133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4133_, 0, v___x_4132_);
                crate::leanh::lean_ctor_set(v___x_4133_, 1, v_a_3743_);
                return v___x_4133_;
            }
            11 => {
                crate::leanh::lean_inc(v___x_4162_);
                v___x_4173_ =
                    l_Lean_Syntax_node2(v___x_4162_, v___x_4170_, v___y_4172_, v___x_4161_);
                v___x_4174_ =
                    l_Lean_Syntax_node2(v___x_4162_, v___x_4163_, v___x_4169_, v___x_4173_);
                v___x_4175_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4175_, 0, v___x_4174_);
                crate::leanh::lean_ctor_set(v___x_4175_, 1, v_a_3743_);
                return v___x_4175_;
            }
            12 => {
                crate::leanh::lean_inc(v___x_4201_);
                v___x_4212_ =
                    l_Lean_Syntax_node2(v___x_4201_, v___x_4209_, v___y_4211_, v___x_4195_);
                v___x_4213_ =
                    l_Lean_Syntax_node2(v___x_4201_, v___x_4202_, v___x_4208_, v___x_4212_);
                v___x_4214_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4214_, 0, v___x_4213_);
                crate::leanh::lean_ctor_set(v___x_4214_, 1, v_a_3743_);
                return v___x_4214_;
            }
            13 => {
                v___x_4244_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_4245_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                crate::leanh::lean_inc_n(v___x_4233_, 3);
                v___x_4246_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4246_, 0, v___x_4233_);
                crate::leanh::lean_ctor_set(v___x_4246_, 1, v___x_4245_);
                v___x_4247_ =
                    l_Lean_Syntax_node2(v___x_4233_, v___x_4244_, v___x_4246_, v___x_4195_);
                v___x_4248_ =
                    l_Lean_Syntax_node2(v___x_4233_, v___x_4241_, v___y_4243_, v___x_4247_);
                v___x_4249_ =
                    l_Lean_Syntax_node2(v___x_4233_, v___x_4234_, v___x_4240_, v___x_4248_);
                v___x_4250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4250_, 0, v___x_4249_);
                crate::leanh::lean_ctor_set(v___x_4250_, 1, v_a_3743_);
                return v___x_4250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed(
    mut v_x_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4268_ =
        l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(v_x_4265_, v_a_4266_, v_a_4267_);
    crate::leanh::lean_dec_ref(v_a_4266_);
    return v_res_4268_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(
    mut v_a_4269_: *mut crate::leanh::LeanObject,
    mut v_b_4270_: *mut crate::leanh::LeanObject,
    mut v_x_4271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4271_) == 0 {
                    crate::leanh::lean_dec(v_b_4270_);
                    crate::leanh::lean_dec(v_a_4269_);
                    return v_x_4271_;
                } else {
                    v_key_4272_ = crate::leanh::lean_ctor_get(v_x_4271_, 0);
                    v_value_4273_ = crate::leanh::lean_ctor_get(v_x_4271_, 1);
                    v_tail_4274_ = crate::leanh::lean_ctor_get(v_x_4271_, 2);
                    v_isSharedCheck_4286_ = (!crate::leanh::lean_is_exclusive(v_x_4271_)) as u8;
                    if v_isSharedCheck_4286_ == 0 {
                        v___x_4276_ = v_x_4271_;
                        v_isShared_4277_ = v_isSharedCheck_4286_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4274_);
                        crate::leanh::lean_inc(v_value_4273_);
                        crate::leanh::lean_inc(v_key_4272_);
                        crate::leanh::lean_dec(v_x_4271_);
                        v___x_4276_ = crate::leanh::lean_box(0);
                        v_isShared_4277_ = v_isSharedCheck_4286_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4278_ = lean_name_eq(v_key_4272_, v_a_4269_);
                if v___x_4278_ == 0 {
                    v___x_4279_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_4269_, v_b_4270_, v_tail_4274_);
                    if v_isShared_4277_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4276_, 2, v___x_4279_);
                        v___x_4281_ = v___x_4276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4282_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_key_4272_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_value_4273_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4282_, 2, v___x_4279_);
                        v___x_4281_ = v_reuseFailAlloc_4282_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_4273_);
                    crate::leanh::lean_dec(v_key_4272_);
                    if v_isShared_4277_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4276_, 1, v_b_4270_);
                        crate::leanh::lean_ctor_set(v___x_4276_, 0, v_a_4269_);
                        v___x_4284_ = v___x_4276_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4285_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4269_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_b_4270_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_tail_4274_);
                        v___x_4284_ = v_reuseFailAlloc_4285_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4281_;
            }
            3 => {
                return v___x_4284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u64 = 0;
    v___x_4287_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4288_ = lean_uint64_of_nat(v___x_4287_);
    return v___x_4288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_4289_: *mut crate::leanh::LeanObject,
    mut v_x_4290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4299_: u64 = 0;
    let mut v___x_4300_: u64 = 0;
    let mut v___x_4301_: u64 = 0;
    let mut v_fold_4302_: u64 = 0;
    let mut v___x_4303_: u64 = 0;
    let mut v___x_4304_: u64 = 0;
    let mut v___x_4305_: u64 = 0;
    let mut v___x_4306_: usize = 0;
    let mut v___x_4307_: usize = 0;
    let mut v___x_4308_: usize = 0;
    let mut v___x_4309_: usize = 0;
    let mut v___x_4310_: usize = 0;
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u64 = 0;
    let mut v_hash_4318_: u64 = 0;
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4290_) == 0 {
                    return v_x_4289_;
                } else {
                    v_key_4291_ = crate::leanh::lean_ctor_get(v_x_4290_, 0);
                    v_value_4292_ = crate::leanh::lean_ctor_get(v_x_4290_, 1);
                    v_tail_4293_ = crate::leanh::lean_ctor_get(v_x_4290_, 2);
                    v_isSharedCheck_4319_ = (!crate::leanh::lean_is_exclusive(v_x_4290_)) as u8;
                    if v_isSharedCheck_4319_ == 0 {
                        v___x_4295_ = v_x_4290_;
                        v_isShared_4296_ = v_isSharedCheck_4319_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4293_);
                        crate::leanh::lean_inc(v_value_4292_);
                        crate::leanh::lean_inc(v_key_4291_);
                        crate::leanh::lean_dec(v_x_4290_);
                        v___x_4295_ = crate::leanh::lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4319_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4297_ = lean_array_get_size(v_x_4289_);
                if crate::leanh::lean_obj_tag(v_key_4291_) == 0 {
                    v___x_4317_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4299_ = v___x_4317_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4318_ = crate::leanh::lean_ctor_get_uint64(
                        v_key_4291_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4299_ = v_hash_4318_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4300_ = 32u64;
                v___x_4301_ = lean_uint64_shift_right(v___y_4299_, v___x_4300_);
                v_fold_4302_ = lean_uint64_xor(v___y_4299_, v___x_4301_);
                v___x_4303_ = 16u64;
                v___x_4304_ = lean_uint64_shift_right(v_fold_4302_, v___x_4303_);
                v___x_4305_ = lean_uint64_xor(v_fold_4302_, v___x_4304_);
                v___x_4306_ = lean_uint64_to_usize(v___x_4305_);
                v___x_4307_ = lean_usize_of_nat(v___x_4297_);
                v___x_4308_ = 1usize;
                v___x_4309_ = lean_usize_sub(v___x_4307_, v___x_4308_);
                v___x_4310_ = lean_usize_land(v___x_4306_, v___x_4309_);
                v___x_4311_ = lean_array_uget_borrowed(v_x_4289_, v___x_4310_);
                crate::leanh::lean_inc(v___x_4311_);
                if v_isShared_4296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4295_, 2, v___x_4311_);
                    v___x_4313_ = v___x_4295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4316_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_key_4291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_value_4292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4316_, 2, v___x_4311_);
                    v___x_4313_ = v_reuseFailAlloc_4316_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4314_ = lean_array_uset(v_x_4289_, v___x_4310_, v___x_4313_);
                v_x_4289_ = v___x_4314_;
                v_x_4290_ = v_tail_4293_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_i_4320_: *mut crate::leanh::LeanObject,
    mut v_source_4321_: *mut crate::leanh::LeanObject,
    mut v_target_4322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v_es_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4323_ = lean_array_get_size(v_source_4321_);
                v___x_4324_ = lean_nat_dec_lt(v_i_4320_, v___x_4323_);
                if v___x_4324_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_4321_);
                    crate::leanh::lean_dec(v_i_4320_);
                    return v_target_4322_;
                } else {
                    v_es_4325_ = lean_array_fget(v_source_4321_, v_i_4320_);
                    v___x_4326_ = crate::leanh::lean_box(0);
                    v_source_4327_ = lean_array_fset(v_source_4321_, v_i_4320_, v___x_4326_);
                    v_target_4328_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_4322_, v_es_4325_);
                    v___x_4329_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4330_ = lean_nat_add(v_i_4320_, v___x_4329_);
                    crate::leanh::lean_dec(v_i_4320_);
                    v_i_4320_ = v___x_4330_;
                    v_source_4321_ = v_source_4327_;
                    v_target_4322_ = v_target_4328_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(
    mut v_data_4332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4333_ = lean_array_get_size(v_data_4332_);
    v___x_4334_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_4335_ = lean_nat_mul(v___x_4333_, v___x_4334_);
    v___x_4336_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4337_ = crate::leanh::lean_box(0);
    v___x_4338_ = lean_mk_array(v_nbuckets_4335_, v___x_4337_);
    v___x_4339_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_4336_, v_data_4332_, v___x_4338_);
    return v___x_4339_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(
    mut v_a_4340_: *mut crate::leanh::LeanObject,
    mut v_x_4341_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4342_: u8 = 0;
    let mut v_key_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4341_) == 0 {
                    v___x_4342_ = 0;
                    return v___x_4342_;
                } else {
                    v_key_4343_ = crate::leanh::lean_ctor_get(v_x_4341_, 0);
                    v_tail_4344_ = crate::leanh::lean_ctor_get(v_x_4341_, 2);
                    v___x_4345_ = lean_name_eq(v_key_4343_, v_a_4340_);
                    if v___x_4345_ == 0 {
                        v_x_4341_ = v_tail_4344_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4345_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_a_4347_: *mut crate::leanh::LeanObject,
    mut v_x_4348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4349_: u8 = 0;
    let mut v_r_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_4347_, v_x_4348_);
    crate::leanh::lean_dec(v_x_4348_);
    crate::leanh::lean_dec(v_a_4347_);
    v_r_4350_ = crate::leanh::lean_box((v_res_4349_) as usize);
    return v_r_4350_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(
    mut v_m_4351_: *mut crate::leanh::LeanObject,
    mut v_a_4352_: *mut crate::leanh::LeanObject,
    mut v_b_4353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: u64 = 0;
    let mut v___x_4362_: u64 = 0;
    let mut v___x_4363_: u64 = 0;
    let mut v_fold_4364_: u64 = 0;
    let mut v___x_4365_: u64 = 0;
    let mut v___x_4366_: u64 = 0;
    let mut v___x_4367_: u64 = 0;
    let mut v___x_4368_: usize = 0;
    let mut v___x_4369_: usize = 0;
    let mut v___x_4370_: usize = 0;
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: usize = 0;
    let mut v_bkt_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v_val_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u64 = 0;
    let mut v_hash_4400_: u64 = 0;
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4354_ = crate::leanh::lean_ctor_get(v_m_4351_, 0);
                v_buckets_4355_ = crate::leanh::lean_ctor_get(v_m_4351_, 1);
                v_isSharedCheck_4401_ = (!crate::leanh::lean_is_exclusive(v_m_4351_)) as u8;
                if v_isSharedCheck_4401_ == 0 {
                    v___x_4357_ = v_m_4351_;
                    v_isShared_4358_ = v_isSharedCheck_4401_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_4355_);
                    crate::leanh::lean_inc(v_size_4354_);
                    crate::leanh::lean_dec(v_m_4351_);
                    v___x_4357_ = crate::leanh::lean_box(0);
                    v_isShared_4358_ = v_isSharedCheck_4401_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4359_ = lean_array_get_size(v_buckets_4355_);
                if crate::leanh::lean_obj_tag(v_a_4352_) == 0 {
                    v___x_4399_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4361_ = v___x_4399_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4400_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4352_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4361_ = v_hash_4400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4362_ = 32u64;
                v___x_4363_ = lean_uint64_shift_right(v___y_4361_, v___x_4362_);
                v_fold_4364_ = lean_uint64_xor(v___y_4361_, v___x_4363_);
                v___x_4365_ = 16u64;
                v___x_4366_ = lean_uint64_shift_right(v_fold_4364_, v___x_4365_);
                v___x_4367_ = lean_uint64_xor(v_fold_4364_, v___x_4366_);
                v___x_4368_ = lean_uint64_to_usize(v___x_4367_);
                v___x_4369_ = lean_usize_of_nat(v___x_4359_);
                v___x_4370_ = 1usize;
                v___x_4371_ = lean_usize_sub(v___x_4369_, v___x_4370_);
                v___x_4372_ = lean_usize_land(v___x_4368_, v___x_4371_);
                v_bkt_4373_ = lean_array_uget_borrowed(v_buckets_4355_, v___x_4372_);
                v___x_4374_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_4352_, v_bkt_4373_);
                if v___x_4374_ == 0 {
                    v___x_4375_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_4376_ = lean_nat_add(v_size_4354_, v___x_4375_);
                    crate::leanh::lean_dec(v_size_4354_);
                    crate::leanh::lean_inc(v_bkt_4373_);
                    v___x_4377_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4377_, 0, v_a_4352_);
                    crate::leanh::lean_ctor_set(v___x_4377_, 1, v_b_4353_);
                    crate::leanh::lean_ctor_set(v___x_4377_, 2, v_bkt_4373_);
                    v_buckets_x27_4378_ =
                        lean_array_uset(v_buckets_4355_, v___x_4372_, v___x_4377_);
                    v___x_4379_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4380_ = lean_nat_mul(v_size_x27_4376_, v___x_4379_);
                    v___x_4381_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_4382_ = lean_nat_div(v___x_4380_, v___x_4381_);
                    crate::leanh::lean_dec(v___x_4380_);
                    v___x_4383_ = lean_array_get_size(v_buckets_x27_4378_);
                    v___x_4384_ = lean_nat_dec_le(v___x_4382_, v___x_4383_);
                    crate::leanh::lean_dec(v___x_4382_);
                    if v___x_4384_ == 0 {
                        v_val_4385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_4378_);
                        if v_isShared_4358_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4357_, 1, v_val_4385_);
                            crate::leanh::lean_ctor_set(v___x_4357_, 0, v_size_x27_4376_);
                            v___x_4387_ = v___x_4357_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4388_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4388_,
                                0,
                                v_size_x27_4376_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_val_4385_);
                            v___x_4387_ = v_reuseFailAlloc_4388_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4358_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4357_, 1, v_buckets_x27_4378_);
                            crate::leanh::lean_ctor_set(v___x_4357_, 0, v_size_x27_4376_);
                            v___x_4390_ = v___x_4357_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4391_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4391_,
                                0,
                                v_size_x27_4376_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_4391_,
                                1,
                                v_buckets_x27_4378_,
                            );
                            v___x_4390_ = v_reuseFailAlloc_4391_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_4373_);
                    v___x_4392_ = crate::leanh::lean_box(0);
                    v_buckets_x27_4393_ =
                        lean_array_uset(v_buckets_4355_, v___x_4372_, v___x_4392_);
                    v___x_4394_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_4352_, v_b_4353_, v_bkt_4373_);
                    v___x_4395_ = lean_array_uset(v_buckets_x27_4393_, v___x_4372_, v___x_4394_);
                    if v_isShared_4358_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4357_, 1, v___x_4395_);
                        v___x_4397_ = v___x_4357_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4398_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_size_4354_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4398_, 1, v___x_4395_);
                        v___x_4397_ = v_reuseFailAlloc_4398_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4387_;
            }
            4 => {
                return v___x_4390_;
            }
            5 => {
                return v___x_4397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(
    mut v_as_x27_4402_: *mut crate::leanh::LeanObject,
    mut v_b_4403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4402_) == 0 {
                    return v_b_4403_;
                } else {
                    v_head_4404_ = crate::leanh::lean_ctor_get(v_as_x27_4402_, 0);
                    v_tail_4405_ = crate::leanh::lean_ctor_get(v_as_x27_4402_, 1);
                    v_fst_4406_ = crate::leanh::lean_ctor_get(v_head_4404_, 0);
                    v_snd_4407_ = crate::leanh::lean_ctor_get(v_head_4404_, 1);
                    crate::leanh::lean_inc(v_snd_4407_);
                    crate::leanh::lean_inc(v_fst_4406_);
                    v_r_4408_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_b_4403_, v_fst_4406_, v_snd_4407_);
                    v_as_x27_4402_ = v_tail_4405_;
                    v_b_4403_ = v_r_4408_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg___boxed(
    mut v_as_x27_4410_: *mut crate::leanh::LeanObject,
    mut v_b_4411_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4412_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_4410_, v_b_4411_);
    crate::leanh::lean_dec(v_as_x27_4410_);
    return v_res_4412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(
    mut v_m_4413_: *mut crate::leanh::LeanObject,
    mut v_l_4414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4415_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_4414_, v_m_4413_);
    return v___x_4415_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(
    mut v_m_4416_: *mut crate::leanh::LeanObject,
    mut v_l_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(v_m_4416_, v_l_4417_);
    crate::leanh::lean_dec(v_l_4417_);
    return v_res_4418_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4481_ = crate::leanh::lean_box(0);
    v___x_4482_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4483_ = lean_mk_array(v___x_4482_, v___x_4481_);
    return v___x_4483_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4484_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once), _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
    v___x_4485_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4486_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4486_, 0, v___x_4485_);
    crate::leanh::lean_ctor_set(v___x_4486_, 1, v___x_4484_);
    return v___x_4486_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4487_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once), _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
    v___x_4488_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21;
    v___x_4489_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_4488_, v___x_4487_);
    return v___x_4489_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4490_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once), _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
    return v___x_4490_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(
    mut v_00_u03b2_4491_: *mut crate::leanh::LeanObject,
    mut v_m_4492_: *mut crate::leanh::LeanObject,
    mut v_a_4493_: *mut crate::leanh::LeanObject,
    mut v_b_4494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_4492_, v_a_4493_, v_b_4494_);
    return v___x_4495_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(
    mut v_as_4496_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4497_: *mut crate::leanh::LeanObject,
    mut v_b_4498_: *mut crate::leanh::LeanObject,
    mut v_a_4499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4500_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_4497_, v_b_4498_);
    return v___x_4500_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(
    mut v_as_4501_: *mut crate::leanh::LeanObject,
    mut v_as_x27_4502_: *mut crate::leanh::LeanObject,
    mut v_b_4503_: *mut crate::leanh::LeanObject,
    mut v_a_4504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4505_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_4501_, v_as_x27_4502_, v_b_4503_, v_a_4504_);
    crate::leanh::lean_dec(v_as_x27_4502_);
    crate::leanh::lean_dec(v_as_4501_);
    return v_res_4505_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4506_: *mut crate::leanh::LeanObject,
    mut v_a_4507_: *mut crate::leanh::LeanObject,
    mut v_x_4508_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4509_: u8 = 0;
    v___x_4509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_4507_, v_x_4508_);
    return v___x_4509_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4510_: *mut crate::leanh::LeanObject,
    mut v_a_4511_: *mut crate::leanh::LeanObject,
    mut v_x_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4513_: u8 = 0;
    let mut v_r_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_4510_, v_a_4511_, v_x_4512_);
    crate::leanh::lean_dec(v_x_4512_);
    crate::leanh::lean_dec(v_a_4511_);
    v_r_4514_ = crate::leanh::lean_box((v_res_4513_) as usize);
    return v_r_4514_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4515_: *mut crate::leanh::LeanObject,
    mut v_data_4516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_4516_);
    return v___x_4517_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(
    mut v_00_u03b2_4518_: *mut crate::leanh::LeanObject,
    mut v_a_4519_: *mut crate::leanh::LeanObject,
    mut v_b_4520_: *mut crate::leanh::LeanObject,
    mut v_x_4521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4522_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_4519_, v_b_4520_, v_x_4521_);
    return v___x_4522_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_4523_: *mut crate::leanh::LeanObject,
    mut v_i_4524_: *mut crate::leanh::LeanObject,
    mut v_source_4525_: *mut crate::leanh::LeanObject,
    mut v_target_4526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4527_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_4524_, v_source_4525_, v_target_4526_);
    return v___x_4527_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_4528_: *mut crate::leanh::LeanObject,
    mut v_x_4529_: *mut crate::leanh::LeanObject,
    mut v_x_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4531_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_4529_, v_x_4530_);
    return v___x_4531_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(
    mut v_name_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = lean_st_ref_get(v___y_4533_);
    v_env_4536_ = crate::leanh::lean_ctor_get(v___x_4535_, 0);
    crate::leanh::lean_inc_ref(v_env_4536_);
    crate::leanh::lean_dec(v___x_4535_);
    v___x_4537_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_4538_ = crate::leanh::lean_ctor_get(v___x_4537_, 0);
    v_asyncMode_4539_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4538_, 2);
    v___x_4540_ = crate::leanh::lean_box(1);
    v___x_4541_ = crate::leanh::lean_box(0);
    v___x_4542_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_4540_,
        v___x_4537_,
        v_env_4536_,
        v_asyncMode_4539_,
        v___x_4541_,
    );
    v___x_4543_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v___x_4542_,
            v_name_4532_,
        );
    crate::leanh::lean_dec(v___x_4542_);
    v___x_4544_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4544_, 0, v___x_4543_);
    return v___x_4544_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(
    mut v_name_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_4545_, v___y_4546_);
    crate::leanh::lean_dec(v___y_4546_);
    crate::leanh::lean_dec(v_name_4545_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(
    mut v_name_4549_: *mut crate::leanh::LeanObject,
    mut v___y_4550_: *mut crate::leanh::LeanObject,
    mut v___y_4551_: *mut crate::leanh::LeanObject,
    mut v___y_4552_: *mut crate::leanh::LeanObject,
    mut v___y_4553_: *mut crate::leanh::LeanObject,
    mut v___y_4554_: *mut crate::leanh::LeanObject,
    mut v___y_4555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4557_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_4549_, v___y_4555_);
    return v___x_4557_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(
    mut v_name_4558_: *mut crate::leanh::LeanObject,
    mut v___y_4559_: *mut crate::leanh::LeanObject,
    mut v___y_4560_: *mut crate::leanh::LeanObject,
    mut v___y_4561_: *mut crate::leanh::LeanObject,
    mut v___y_4562_: *mut crate::leanh::LeanObject,
    mut v___y_4563_: *mut crate::leanh::LeanObject,
    mut v___y_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4566_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
    crate::leanh::lean_dec(v___y_4564_);
    crate::leanh::lean_dec_ref(v___y_4563_);
    crate::leanh::lean_dec(v___y_4562_);
    crate::leanh::lean_dec_ref(v___y_4561_);
    crate::leanh::lean_dec(v___y_4560_);
    crate::leanh::lean_dec_ref(v___y_4559_);
    crate::leanh::lean_dec(v_name_4558_);
    return v_res_4566_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(
    mut v_msgData_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4573_ = lean_st_ref_get(v___y_4571_);
    v_env_4574_ = crate::leanh::lean_ctor_get(v___x_4573_, 0);
    crate::leanh::lean_inc_ref(v_env_4574_);
    crate::leanh::lean_dec(v___x_4573_);
    v___x_4575_ = lean_st_ref_get(v___y_4569_);
    v_mctx_4576_ = crate::leanh::lean_ctor_get(v___x_4575_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4576_);
    crate::leanh::lean_dec(v___x_4575_);
    v_lctx_4577_ = crate::leanh::lean_ctor_get(v___y_4568_, 2);
    v_options_4578_ = crate::leanh::lean_ctor_get(v___y_4570_, 2);
    crate::leanh::lean_inc_ref(v_options_4578_);
    crate::leanh::lean_inc_ref(v_lctx_4577_);
    v___x_4579_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4579_, 0, v_env_4574_);
    crate::leanh::lean_ctor_set(v___x_4579_, 1, v_mctx_4576_);
    crate::leanh::lean_ctor_set(v___x_4579_, 2, v_lctx_4577_);
    crate::leanh::lean_ctor_set(v___x_4579_, 3, v_options_4578_);
    v___x_4580_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4580_, 0, v___x_4579_);
    crate::leanh::lean_ctor_set(v___x_4580_, 1, v_msgData_4567_);
    v___x_4581_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4581_, 0, v___x_4580_);
    return v___x_4581_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(
    mut v_msgData_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
    mut v___y_4587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4588_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
    crate::leanh::lean_dec(v___y_4586_);
    crate::leanh::lean_dec_ref(v___y_4585_);
    crate::leanh::lean_dec(v___y_4584_);
    crate::leanh::lean_dec_ref(v___y_4583_);
    return v_res_4588_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: f64 = 0.0;
    v___x_4589_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4590_ = lean_float_of_nat(v___x_4589_);
    return v___x_4590_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(
    mut v_cls_4594_: *mut crate::leanh::LeanObject,
    mut v_msg_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4619_: u8 = 0;
    let mut v_tid_4620_: u64 = 0;
    let mut v_traces_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___x_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: f64 = 0.0;
    let mut v___x_4627_: u8 = 0;
    let mut v___x_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_isSharedCheck_4647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4601_ = crate::leanh::lean_ctor_get(v___y_4598_, 5);
                v___x_4602_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
                v_a_4603_ = crate::leanh::lean_ctor_get(v___x_4602_, 0);
                v_isSharedCheck_4647_ = (!crate::leanh::lean_is_exclusive(v___x_4602_)) as u8;
                if v_isSharedCheck_4647_ == 0 {
                    v___x_4605_ = v___x_4602_;
                    v_isShared_4606_ = v_isSharedCheck_4647_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4603_);
                    crate::leanh::lean_dec(v___x_4602_);
                    v___x_4605_ = crate::leanh::lean_box(0);
                    v_isShared_4606_ = v_isSharedCheck_4647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4607_ = lean_st_ref_take(v___y_4599_);
                v_traceState_4608_ = crate::leanh::lean_ctor_get(v___x_4607_, 4);
                v_env_4609_ = crate::leanh::lean_ctor_get(v___x_4607_, 0);
                v_nextMacroScope_4610_ = crate::leanh::lean_ctor_get(v___x_4607_, 1);
                v_ngen_4611_ = crate::leanh::lean_ctor_get(v___x_4607_, 2);
                v_auxDeclNGen_4612_ = crate::leanh::lean_ctor_get(v___x_4607_, 3);
                v_cache_4613_ = crate::leanh::lean_ctor_get(v___x_4607_, 5);
                v_messages_4614_ = crate::leanh::lean_ctor_get(v___x_4607_, 6);
                v_infoState_4615_ = crate::leanh::lean_ctor_get(v___x_4607_, 7);
                v_snapshotTasks_4616_ = crate::leanh::lean_ctor_get(v___x_4607_, 8);
                v_isSharedCheck_4646_ = (!crate::leanh::lean_is_exclusive(v___x_4607_)) as u8;
                if v_isSharedCheck_4646_ == 0 {
                    v___x_4618_ = v___x_4607_;
                    v_isShared_4619_ = v_isSharedCheck_4646_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4616_);
                    crate::leanh::lean_inc(v_infoState_4615_);
                    crate::leanh::lean_inc(v_messages_4614_);
                    crate::leanh::lean_inc(v_cache_4613_);
                    crate::leanh::lean_inc(v_traceState_4608_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4612_);
                    crate::leanh::lean_inc(v_ngen_4611_);
                    crate::leanh::lean_inc(v_nextMacroScope_4610_);
                    crate::leanh::lean_inc(v_env_4609_);
                    crate::leanh::lean_dec(v___x_4607_);
                    v___x_4618_ = crate::leanh::lean_box(0);
                    v_isShared_4619_ = v_isSharedCheck_4646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4620_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_4608_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_4621_ = crate::leanh::lean_ctor_get(v_traceState_4608_, 0);
                v_isSharedCheck_4645_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_4608_)) as u8;
                if v_isSharedCheck_4645_ == 0 {
                    v___x_4623_ = v_traceState_4608_;
                    v_isShared_4624_ = v_isSharedCheck_4645_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_4621_);
                    crate::leanh::lean_dec(v_traceState_4608_);
                    v___x_4623_ = crate::leanh::lean_box(0);
                    v_isShared_4624_ = v_isSharedCheck_4645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4625_ = crate::leanh::lean_box(0);
                v___x_4626_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
                v___x_4627_ = 0;
                v___x_4628_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                v___x_4629_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_4629_, 0, v_cls_4594_);
                crate::leanh::lean_ctor_set(v___x_4629_, 1, v___x_4625_);
                crate::leanh::lean_ctor_set(v___x_4629_, 2, v___x_4628_);
                crate::leanh::lean_ctor_set_float(
                    v___x_4629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_4626_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_4629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_4626_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4629_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_4627_,
                );
                v___x_4630_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2;
                v___x_4631_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4631_, 0, v___x_4629_);
                crate::leanh::lean_ctor_set(v___x_4631_, 1, v_a_4603_);
                crate::leanh::lean_ctor_set(v___x_4631_, 2, v___x_4630_);
                crate::leanh::lean_inc(v_ref_4601_);
                v___x_4632_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4632_, 0, v_ref_4601_);
                crate::leanh::lean_ctor_set(v___x_4632_, 1, v___x_4631_);
                v___x_4633_ = l_Lean_PersistentArray_push___redArg(v_traces_4621_, v___x_4632_);
                if v_isShared_4624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4623_, 0, v___x_4633_);
                    v___x_4635_ = v___x_4623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4633_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_4644_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_4620_,
                    );
                    v___x_4635_ = v_reuseFailAlloc_4644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4619_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4618_, 4, v___x_4635_);
                    v___x_4637_ = v___x_4618_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4643_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_env_4609_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 1, v_nextMacroScope_4610_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 2, v_ngen_4611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 3, v_auxDeclNGen_4612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 4, v___x_4635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 5, v_cache_4613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 6, v_messages_4614_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 7, v_infoState_4615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4643_, 8, v_snapshotTasks_4616_);
                    v___x_4637_ = v_reuseFailAlloc_4643_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4638_ = lean_st_ref_set(v___y_4599_, v___x_4637_);
                v___x_4639_ = crate::leanh::lean_box(0);
                if v_isShared_4606_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4605_, 0, v___x_4639_);
                    v___x_4641_ = v___x_4605_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
                    v___x_4641_ = v_reuseFailAlloc_4642_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___boxed(
    mut v_cls_4648_: *mut crate::leanh::LeanObject,
    mut v_msg_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
    mut v___y_4654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_4648_, v_msg_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
    crate::leanh::lean_dec(v___y_4653_);
    crate::leanh::lean_dec_ref(v___y_4652_);
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4650_);
    return v_res_4655_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(
    mut v_as_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
    mut v___y_4661_: *mut crate::leanh::LeanObject,
    mut v___y_4662_: *mut crate::leanh::LeanObject,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4670_: u8 = 0;
    let mut v_tail_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_4659_) == 0 {
                    v___x_4667_ = crate::leanh::lean_box(0);
                    v___x_4668_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4668_, 0, v___x_4667_);
                    return v___x_4668_;
                } else {
                    v_options_4669_ = crate::leanh::lean_ctor_get(v___y_4664_, 2);
                    v_hasTrace_4670_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4669_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4670_ == 0 {
                        v_tail_4671_ = crate::leanh::lean_ctor_get(v_as_4659_, 1);
                        crate::leanh::lean_inc(v_tail_4671_);
                        crate::leanh::lean_dec_ref_known(v_as_4659_, 2);
                        v_as_4659_ = v_tail_4671_;
                        state = 0;
                        continue;
                    } else {
                        v_head_4673_ = crate::leanh::lean_ctor_get(v_as_4659_, 0);
                        crate::leanh::lean_inc(v_head_4673_);
                        v_tail_4674_ = crate::leanh::lean_ctor_get(v_as_4659_, 1);
                        crate::leanh::lean_inc(v_tail_4674_);
                        crate::leanh::lean_dec_ref_known(v_as_4659_, 2);
                        v_fst_4675_ = crate::leanh::lean_ctor_get(v_head_4673_, 0);
                        crate::leanh::lean_inc_n(v_fst_4675_, 2);
                        v_snd_4676_ = crate::leanh::lean_ctor_get(v_head_4673_, 1);
                        crate::leanh::lean_inc(v_snd_4676_);
                        crate::leanh::lean_dec(v_head_4673_);
                        v_inheritedTraceOptions_4677_ =
                            crate::leanh::lean_ctor_get(v___y_4664_, 13);
                        v___x_4678_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1;
                        v___x_4679_ = l_Lean_Name_append(v___x_4678_, v_fst_4675_);
                        v___x_4680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4677_,
                            v_options_4669_,
                            v___x_4679_,
                        );
                        crate::leanh::lean_dec(v___x_4679_);
                        if v___x_4680_ == 0 {
                            crate::leanh::lean_dec(v_snd_4676_);
                            crate::leanh::lean_dec(v_fst_4675_);
                            v_as_4659_ = v_tail_4674_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4682_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4682_, 0, v_snd_4676_);
                            v___x_4683_ = l_Lean_MessageData_ofFormat(v___x_4682_);
                            v___x_4684_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_4675_, v___x_4683_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
                            if crate::leanh::lean_obj_tag(v___x_4684_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4684_, 1);
                                v_as_4659_ = v_tail_4674_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_4674_);
                                return v___x_4684_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___boxed(
    mut v_as_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4694_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
    crate::leanh::lean_dec(v___y_4692_);
    crate::leanh::lean_dec_ref(v___y_4691_);
    crate::leanh::lean_dec(v___y_4690_);
    crate::leanh::lean_dec_ref(v___y_4689_);
    crate::leanh::lean_dec(v___y_4688_);
    crate::leanh::lean_dec_ref(v___y_4687_);
    return v_res_4694_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4695_ = crate::leanh::lean_box(0);
    v___x_4696_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4697_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4697_, 0, v___x_4696_);
    crate::leanh::lean_ctor_set(v___x_4697_, 1, v___x_4695_);
    return v___x_4697_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4699_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
    v___x_4700_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4700_, 0, v___x_4699_);
    return v___x_4700_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(
    mut v___y_4701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
    return v_res_4702_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4708_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4709_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4709_, 0, v___x_4708_);
    return v___x_4709_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4710_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
    v___x_4711_ = l_Lean_MessageData_ofFormat(v___x_4710_);
    return v___x_4711_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4712_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
    v___x_4713_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2;
    v___x_4714_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4714_, 0, v___x_4713_);
    crate::leanh::lean_ctor_set(v___x_4714_, 1, v___x_4712_);
    return v___x_4714_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(
    mut v_ref_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
    v___x_4718_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4718_, 0, v_ref_4715_);
    crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4717_);
    v___x_4719_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4719_, 0, v___x_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(
    mut v_ref_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_4720_);
    return v_res_4722_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(
    mut v_env_4723_: *mut crate::leanh::LeanObject,
    mut v_declName_4724_: *mut crate::leanh::LeanObject,
    mut v___y_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4727_: u8 = 0;
    let mut v_env_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: u8 = 0;
    let mut v___x_4731_: u8 = 0;
    v___x_4727_ = 0;
    v_env_4728_ = l_Lean_Environment_setExporting(v_env_4723_, v___x_4727_);
    crate::leanh::lean_inc(v_declName_4724_);
    v___x_4729_ = l_Lean_mkPrivateName(v_env_4728_, v_declName_4724_);
    v___x_4730_ = 1;
    crate::leanh::lean_inc_ref(v_env_4728_);
    v___x_4731_ = l_Lean_Environment_contains(v_env_4728_, v___x_4729_, v___x_4730_);
    if v___x_4731_ == 0 {
        let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4733_: u8 = 0;
        let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4732_ = l_Lean_privateToUserName(v_declName_4724_);
        v___x_4733_ = l_Lean_Environment_contains(v_env_4728_, v___x_4732_, v___x_4730_);
        v___x_4734_ = crate::leanh::lean_box((v___x_4733_) as usize);
        v___x_4735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4735_, 0, v___x_4734_);
        crate::leanh::lean_ctor_set(v___x_4735_, 1, v___y_4726_);
        return v___x_4735_;
    } else {
        let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_4728_);
        crate::leanh::lean_dec(v_declName_4724_);
        v___x_4736_ = crate::leanh::lean_box((v___x_4731_) as usize);
        v___x_4737_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4737_, 0, v___x_4736_);
        crate::leanh::lean_ctor_set(v___x_4737_, 1, v___y_4726_);
        return v___x_4737_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(
    mut v_env_4738_: *mut crate::leanh::LeanObject,
    mut v_declName_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_4738_, v_declName_4739_, v___y_4740_, v___y_4741_);
    crate::leanh::lean_dec_ref(v___y_4740_);
    return v_res_4742_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(
    mut v_x_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4743_) == 0 {
        let mut v_a_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4745_ = crate::leanh::lean_ctor_get(v_x_4743_, 0);
        crate::leanh::lean_inc(v_a_4745_);
        v___x_4746_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4746_, 0, v_a_4745_);
        crate::leanh::lean_ctor_set(v___x_4746_, 1, v___y_4744_);
        return v___x_4746_;
    } else {
        let mut v_a_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4747_ = crate::leanh::lean_ctor_get(v_x_4743_, 0);
        crate::leanh::lean_inc(v_a_4747_);
        v___x_4748_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4748_, 0, v_a_4747_);
        crate::leanh::lean_ctor_set(v___x_4748_, 1, v___y_4744_);
        return v___x_4748_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(
    mut v_x_4749_: *mut crate::leanh::LeanObject,
    mut v___y_4750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4751_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_4749_, v___y_4750_);
    crate::leanh::lean_dec_ref(v_x_4749_);
    return v_res_4751_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(
    mut v_env_4752_: *mut crate::leanh::LeanObject,
    mut v_stx_4753_: *mut crate::leanh::LeanObject,
    mut v___y_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut v_unused_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4771_: u8 = 0;
    let mut v_snd_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4782_: u8 = 0;
    let mut v_a_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4795_: u8 = 0;
    let mut v_isSharedCheck_4796_: u8 = 0;
    let mut v_a_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4805_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4756_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_4752_,
                    v_stx_4753_,
                    v___y_4754_,
                    v___y_4755_,
                );
                if crate::leanh::lean_obj_tag(v___x_4756_) == 0 {
                    v_a_4757_ = crate::leanh::lean_ctor_get(v___x_4756_, 0);
                    crate::leanh::lean_inc(v_a_4757_);
                    if crate::leanh::lean_obj_tag(v_a_4757_) == 0 {
                        v_a_4758_ = crate::leanh::lean_ctor_get(v___x_4756_, 1);
                        v_isSharedCheck_4766_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4756_)) as u8;
                        if v_isSharedCheck_4766_ == 0 {
                            v_unused_4767_ = crate::leanh::lean_ctor_get(v___x_4756_, 0);
                            crate::leanh::lean_dec(v_unused_4767_);
                            v___x_4760_ = v___x_4756_;
                            v_isShared_4761_ = v_isSharedCheck_4766_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4758_);
                            crate::leanh::lean_dec(v___x_4756_);
                            v___x_4760_ = crate::leanh::lean_box(0);
                            v_isShared_4761_ = v_isSharedCheck_4766_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_4768_ = crate::leanh::lean_ctor_get(v_a_4757_, 0);
                        v_isSharedCheck_4796_ = (!crate::leanh::lean_is_exclusive(v_a_4757_)) as u8;
                        if v_isSharedCheck_4796_ == 0 {
                            v___x_4770_ = v_a_4757_;
                            v_isShared_4771_ = v_isSharedCheck_4796_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4768_);
                            crate::leanh::lean_dec(v_a_4757_);
                            v___x_4770_ = crate::leanh::lean_box(0);
                            v_isShared_4771_ = v_isSharedCheck_4796_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4797_ = crate::leanh::lean_ctor_get(v___x_4756_, 0);
                    v_a_4798_ = crate::leanh::lean_ctor_get(v___x_4756_, 1);
                    v_isSharedCheck_4805_ = (!crate::leanh::lean_is_exclusive(v___x_4756_)) as u8;
                    if v_isSharedCheck_4805_ == 0 {
                        v___x_4800_ = v___x_4756_;
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4798_);
                        crate::leanh::lean_inc(v_a_4797_);
                        crate::leanh::lean_dec(v___x_4756_);
                        v___x_4800_ = crate::leanh::lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4762_ = crate::leanh::lean_box(0);
                if v_isShared_4761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4760_, 0, v___x_4762_);
                    v___x_4764_ = v___x_4760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4765_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_a_4758_);
                    v___x_4764_ = v_reuseFailAlloc_4765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4764_;
            }
            3 => {
                v_snd_4772_ = crate::leanh::lean_ctor_get(v_val_4768_, 1);
                crate::leanh::lean_inc(v_snd_4772_);
                crate::leanh::lean_dec(v_val_4768_);
                if crate::leanh::lean_obj_tag(v_snd_4772_) == 0 {
                    crate::leanh::lean_del_object(v___x_4770_);
                    v_a_4773_ = crate::leanh::lean_ctor_get(v___x_4756_, 1);
                    crate::leanh::lean_inc(v_a_4773_);
                    crate::leanh::lean_dec_ref_known(v___x_4756_, 2);
                    v_a_4774_ = crate::leanh::lean_ctor_get(v_snd_4772_, 0);
                    v_isSharedCheck_4782_ = (!crate::leanh::lean_is_exclusive(v_snd_4772_)) as u8;
                    if v_isSharedCheck_4782_ == 0 {
                        v___x_4776_ = v_snd_4772_;
                        v_isShared_4777_ = v_isSharedCheck_4782_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4774_);
                        crate::leanh::lean_dec(v_snd_4772_);
                        v___x_4776_ = crate::leanh::lean_box(0);
                        v_isShared_4777_ = v_isSharedCheck_4782_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4783_ = crate::leanh::lean_ctor_get(v___x_4756_, 1);
                    crate::leanh::lean_inc(v_a_4783_);
                    crate::leanh::lean_dec_ref_known(v___x_4756_, 2);
                    v_a_4784_ = crate::leanh::lean_ctor_get(v_snd_4772_, 0);
                    v_isSharedCheck_4795_ = (!crate::leanh::lean_is_exclusive(v_snd_4772_)) as u8;
                    if v_isSharedCheck_4795_ == 0 {
                        v___x_4786_ = v_snd_4772_;
                        v_isShared_4787_ = v_isSharedCheck_4795_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4784_);
                        crate::leanh::lean_dec(v_snd_4772_);
                        v___x_4786_ = crate::leanh::lean_box(0);
                        v_isShared_4787_ = v_isSharedCheck_4795_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4777_ == 0 {
                    v___x_4779_ = v___x_4776_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4781_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4774_);
                    v___x_4779_ = v_reuseFailAlloc_4781_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4780_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_4779_, v_a_4773_);
                crate::leanh::lean_dec_ref(v___x_4779_);
                return v___x_4780_;
            }
            6 => {
                if v_isShared_4771_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4770_, 0, v_a_4784_);
                    v___x_4789_ = v___x_4770_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4784_);
                    v___x_4789_ = v_reuseFailAlloc_4794_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4787_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4786_, 0, v___x_4789_);
                    v___x_4791_ = v___x_4786_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4789_);
                    v___x_4791_ = v_reuseFailAlloc_4793_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4792_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_4791_, v_a_4783_);
                crate::leanh::lean_dec_ref(v___x_4791_);
                return v___x_4792_;
            }
            9 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_a_4798_);
                    v___x_4803_ = v_reuseFailAlloc_4804_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed(
    mut v_env_4806_: *mut crate::leanh::LeanObject,
    mut v_stx_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4810_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_4806_, v_stx_4807_, v___y_4808_, v___y_4809_);
    crate::leanh::lean_dec_ref(v___y_4808_);
    return v_res_4810_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(
    mut v_env_4811_: *mut crate::leanh::LeanObject,
    mut v_options_4812_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4813_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4814_: *mut crate::leanh::LeanObject,
    mut v_n_4815_: *mut crate::leanh::LeanObject,
    mut v___y_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4818_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_4811_,
        v_options_4812_,
        v_currNamespace_4813_,
        v_openDecls_4814_,
        v_n_4815_,
    );
    v___x_4819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4819_, 0, v___x_4818_);
    crate::leanh::lean_ctor_set(v___x_4819_, 1, v___y_4817_);
    return v___x_4819_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(
    mut v_env_4820_: *mut crate::leanh::LeanObject,
    mut v_options_4821_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4822_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4823_: *mut crate::leanh::LeanObject,
    mut v_n_4824_: *mut crate::leanh::LeanObject,
    mut v___y_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4827_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_4820_, v_options_4821_, v_currNamespace_4822_, v_openDecls_4823_, v_n_4824_, v___y_4825_, v___y_4826_);
    crate::leanh::lean_dec_ref(v___y_4825_);
    crate::leanh::lean_dec_ref(v_options_4821_);
    return v_res_4827_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(
    mut v_currNamespace_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
    mut v___y_4830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4831_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4831_, 0, v_currNamespace_4828_);
    crate::leanh::lean_ctor_set(v___x_4831_, 1, v___y_4830_);
    return v___x_4831_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(
    mut v_currNamespace_4832_: *mut crate::leanh::LeanObject,
    mut v___y_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4835_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_4832_, v___y_4833_, v___y_4834_);
    crate::leanh::lean_dec_ref(v___y_4833_);
    return v_res_4835_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(
    mut v_a_4836_: *mut crate::leanh::LeanObject,
    mut v_x_4837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4837_) == 0 {
                    v___x_4838_ = crate::leanh::lean_box(0);
                    return v___x_4838_;
                } else {
                    v_key_4839_ = crate::leanh::lean_ctor_get(v_x_4837_, 0);
                    v_value_4840_ = crate::leanh::lean_ctor_get(v_x_4837_, 1);
                    v_tail_4841_ = crate::leanh::lean_ctor_get(v_x_4837_, 2);
                    v___x_4842_ = lean_name_eq(v_key_4839_, v_a_4836_);
                    if v___x_4842_ == 0 {
                        v_x_4837_ = v_tail_4841_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4840_);
                        v___x_4844_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4844_, 0, v_value_4840_);
                        return v___x_4844_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(
    mut v_a_4845_: *mut crate::leanh::LeanObject,
    mut v_x_4846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_4845_, v_x_4846_);
    crate::leanh::lean_dec(v_x_4846_);
    crate::leanh::lean_dec(v_a_4845_);
    return v_res_4847_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(
    mut v_m_4848_: *mut crate::leanh::LeanObject,
    mut v_a_4849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4853_: u64 = 0;
    let mut v___x_4854_: u64 = 0;
    let mut v___x_4855_: u64 = 0;
    let mut v_fold_4856_: u64 = 0;
    let mut v___x_4857_: u64 = 0;
    let mut v___x_4858_: u64 = 0;
    let mut v___x_4859_: u64 = 0;
    let mut v___x_4860_: usize = 0;
    let mut v___x_4861_: usize = 0;
    let mut v___x_4862_: usize = 0;
    let mut v___x_4863_: usize = 0;
    let mut v___x_4864_: usize = 0;
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u64 = 0;
    let mut v_hash_4868_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4850_ = crate::leanh::lean_ctor_get(v_m_4848_, 1);
                v___x_4851_ = lean_array_get_size(v_buckets_4850_);
                if crate::leanh::lean_obj_tag(v_a_4849_) == 0 {
                    v___x_4867_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4853_ = v___x_4867_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4868_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4849_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4853_ = v_hash_4868_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4854_ = 32u64;
                v___x_4855_ = lean_uint64_shift_right(v___y_4853_, v___x_4854_);
                v_fold_4856_ = lean_uint64_xor(v___y_4853_, v___x_4855_);
                v___x_4857_ = 16u64;
                v___x_4858_ = lean_uint64_shift_right(v_fold_4856_, v___x_4857_);
                v___x_4859_ = lean_uint64_xor(v_fold_4856_, v___x_4858_);
                v___x_4860_ = lean_uint64_to_usize(v___x_4859_);
                v___x_4861_ = lean_usize_of_nat(v___x_4851_);
                v___x_4862_ = 1usize;
                v___x_4863_ = lean_usize_sub(v___x_4861_, v___x_4862_);
                v___x_4864_ = lean_usize_land(v___x_4860_, v___x_4863_);
                v___x_4865_ = lean_array_uget_borrowed(v_buckets_4850_, v___x_4864_);
                v___x_4866_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_4849_, v___x_4865_);
                return v___x_4866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg___boxed(
    mut v_m_4869_: *mut crate::leanh::LeanObject,
    mut v_a_4870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_4869_, v_a_4870_);
    crate::leanh::lean_dec(v_a_4870_);
    crate::leanh::lean_dec_ref(v_m_4869_);
    return v_res_4871_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(
    mut v_keys_4872_: *mut crate::leanh::LeanObject,
    mut v_i_4873_: *mut crate::leanh::LeanObject,
    mut v_k_4874_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v_k_x27_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4875_ = lean_array_get_size(v_keys_4872_);
                v___x_4876_ = lean_nat_dec_lt(v_i_4873_, v___x_4875_);
                if v___x_4876_ == 0 {
                    crate::leanh::lean_dec(v_i_4873_);
                    return v___x_4876_;
                } else {
                    v_k_x27_4877_ = lean_array_fget_borrowed(v_keys_4872_, v_i_4873_);
                    v___x_4878_ = l_Lean_instBEqExtraModUse_beq(v_k_4874_, v_k_x27_4877_);
                    if v___x_4878_ == 0 {
                        v___x_4879_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4880_ = lean_nat_add(v_i_4873_, v___x_4879_);
                        crate::leanh::lean_dec(v_i_4873_);
                        v_i_4873_ = v___x_4880_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4873_);
                        return v___x_4878_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(
    mut v_keys_4882_: *mut crate::leanh::LeanObject,
    mut v_i_4883_: *mut crate::leanh::LeanObject,
    mut v_k_4884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4885_: u8 = 0;
    let mut v_r_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4885_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_4882_, v_i_4883_, v_k_4884_);
    crate::leanh::lean_dec_ref(v_k_4884_);
    crate::leanh::lean_dec_ref(v_keys_4882_);
    v_r_4886_ = crate::leanh::lean_box((v_res_4885_) as usize);
    return v_r_4886_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0()
-> usize {
    let mut v___x_4887_: usize = 0;
    let mut v___x_4888_: usize = 0;
    let mut v___x_4889_: usize = 0;
    v___x_4887_ = 5usize;
    v___x_4888_ = 1usize;
    v___x_4889_ = lean_usize_shift_left(v___x_4888_, v___x_4887_);
    return v___x_4889_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1()
-> usize {
    let mut v___x_4890_: usize = 0;
    let mut v___x_4891_: usize = 0;
    let mut v___x_4892_: usize = 0;
    v___x_4890_ = 1usize;
    v___x_4891_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0);
    v___x_4892_ = lean_usize_sub(v___x_4891_, v___x_4890_);
    return v___x_4892_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(
    mut v_x_4893_: *mut crate::leanh::LeanObject,
    mut v_x_4894_: usize,
    mut v_x_4895_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: usize = 0;
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v_j_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: u8 = 0;
    let mut v_node_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: usize = 0;
    let mut v___x_4908_: u8 = 0;
    let mut v_ks_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4893_) == 0 {
                    v_es_4896_ = crate::leanh::lean_ctor_get(v_x_4893_, 0);
                    v___x_4897_ = crate::leanh::lean_box(2);
                    v___x_4898_ = 5usize;
                    v___x_4899_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1);
                    v___x_4900_ = lean_usize_land(v_x_4894_, v___x_4899_);
                    v_j_4901_ = lean_usize_to_nat(v___x_4900_);
                    v___x_4902_ = lean_array_get_borrowed(v___x_4897_, v_es_4896_, v_j_4901_);
                    crate::leanh::lean_dec(v_j_4901_);
                    match crate::leanh::lean_obj_tag(v___x_4902_) {
                        0 => {
                            v_key_4903_ = crate::leanh::lean_ctor_get(v___x_4902_, 0);
                            v___x_4904_ = l_Lean_instBEqExtraModUse_beq(v_x_4895_, v_key_4903_);
                            return v___x_4904_;
                        }
                        1 => {
                            v_node_4905_ = crate::leanh::lean_ctor_get(v___x_4902_, 0);
                            v___x_4906_ = lean_usize_shift_right(v_x_4894_, v___x_4898_);
                            v_x_4893_ = v_node_4905_;
                            v_x_4894_ = v___x_4906_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4908_ = 0;
                            return v___x_4908_;
                        }
                    }
                } else {
                    v_ks_4909_ = crate::leanh::lean_ctor_get(v_x_4893_, 0);
                    v___x_4910_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_4909_, v___x_4910_, v_x_4895_);
                    return v___x_4911_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(
    mut v_x_4912_: *mut crate::leanh::LeanObject,
    mut v_x_4913_: *mut crate::leanh::LeanObject,
    mut v_x_4914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_20467__boxed_4915_: usize = 0;
    let mut v_res_4916_: u8 = 0;
    let mut v_r_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_20467__boxed_4915_ = crate::leanh::lean_unbox_usize(v_x_4913_);
    crate::leanh::lean_dec(v_x_4913_);
    v_res_4916_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_4912_, v_x_20467__boxed_4915_, v_x_4914_);
    crate::leanh::lean_dec_ref(v_x_4914_);
    crate::leanh::lean_dec_ref(v_x_4912_);
    v_r_4917_ = crate::leanh::lean_box((v_res_4916_) as usize);
    return v_r_4917_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(
    mut v_x_4918_: *mut crate::leanh::LeanObject,
    mut v_x_4919_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4920_: u64 = 0;
    let mut v___x_4921_: usize = 0;
    let mut v___x_4922_: u8 = 0;
    v___x_4920_ = l_Lean_instHashableExtraModUse_hash(v_x_4919_);
    v___x_4921_ = lean_uint64_to_usize(v___x_4920_);
    v___x_4922_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_4918_, v___x_4921_, v_x_4919_);
    return v___x_4922_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg___boxed(
    mut v_x_4923_: *mut crate::leanh::LeanObject,
    mut v_x_4924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4925_: u8 = 0;
    let mut v_r_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4925_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_4923_, v_x_4924_);
    crate::leanh::lean_dec_ref(v_x_4924_);
    crate::leanh::lean_dec_ref(v_x_4923_);
    v_r_4926_ = crate::leanh::lean_box((v_res_4925_) as usize);
    return v_r_4926_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4929_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1;
    v___x_4930_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0;
    v___x_4931_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4930_,
        v___x_4929_,
    );
    return v___x_4931_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4932_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4932_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4933_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
    v___x_4934_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4934_, 0, v___x_4933_);
    return v___x_4934_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4935_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
    v___x_4936_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4936_, 0, v___x_4935_);
    crate::leanh::lean_ctor_set(v___x_4936_, 1, v___x_4935_);
    return v___x_4936_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4937_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
    v___x_4938_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4938_, 0, v___x_4937_);
    crate::leanh::lean_ctor_set(v___x_4938_, 1, v___x_4937_);
    crate::leanh::lean_ctor_set(v___x_4938_, 2, v___x_4937_);
    crate::leanh::lean_ctor_set(v___x_4938_, 3, v___x_4937_);
    crate::leanh::lean_ctor_set(v___x_4938_, 4, v___x_4937_);
    crate::leanh::lean_ctor_set(v___x_4938_, 5, v___x_4937_);
    return v___x_4938_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4943_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9;
    v___x_4944_ = l_Lean_stringToMessageData(v___x_4943_);
    return v___x_4944_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4946_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11;
    v___x_4947_ = l_Lean_stringToMessageData(v___x_4946_);
    return v___x_4947_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4948_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
    v___x_4949_ = l_Lean_stringToMessageData(v___x_4948_);
    return v___x_4949_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_4950_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
    v___x_4951_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1;
    v___x_4952_ = l_Lean_Name_append(v___x_4951_, v_cls_4950_);
    return v___x_4952_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4954_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15;
    v___x_4955_ = l_Lean_stringToMessageData(v___x_4954_);
    return v___x_4955_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4957_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17;
    v___x_4958_ = l_Lean_stringToMessageData(v___x_4957_);
    return v___x_4958_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(
    mut v_mod_4963_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4964_: u8,
    mut v_hint_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
    mut v___y_4967_: *mut crate::leanh::LeanObject,
    mut v___y_4968_: *mut crate::leanh::LeanObject,
    mut v___y_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
    mut v___y_4971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4975_: u8 = 0;
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v_asyncMode_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut v_unused_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v_unused_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: u8 = 0;
    let mut v_options_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5028_: u8 = 0;
    let mut v_inheritedTraceOptions_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: u8 = 0;
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u8 = 0;
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4973_ = lean_st_ref_get(v___y_4971_);
                v_env_4974_ = crate::leanh::lean_ctor_get(v___x_4973_, 0);
                crate::leanh::lean_inc_ref(v_env_4974_);
                crate::leanh::lean_dec(v___x_4973_);
                v_isExporting_4975_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4974_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4974_);
                v___x_4976_ = lean_st_ref_get(v___y_4971_);
                v_env_4977_ = crate::leanh::lean_ctor_get(v___x_4976_, 0);
                crate::leanh::lean_inc_ref(v_env_4977_);
                crate::leanh::lean_dec(v___x_4976_);
                v___x_4978_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
                crate::leanh::lean_inc(v_mod_4963_);
                v_entry_4979_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_4979_, 0, v_mod_4963_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4979_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_4975_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4979_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4964_,
                );
                v___x_4980_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4981_ = crate::leanh::lean_box(1);
                v___x_4982_ = crate::leanh::lean_box(0);
                v___x_5025_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4978_,
                    v___x_4980_,
                    v_env_4977_,
                    v___x_4981_,
                    v___x_4982_,
                );
                v___x_5026_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_5025_, v_entry_4979_);
                crate::leanh::lean_dec(v___x_5025_);
                if v___x_5026_ == 0 {
                    v_options_5027_ = crate::leanh::lean_ctor_get(v___y_4970_, 2);
                    v_hasTrace_5028_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_5027_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5028_ == 0 {
                        crate::leanh::lean_dec(v_hint_4965_);
                        crate::leanh::lean_dec(v_mod_4963_);
                        v___y_4984_ = v___y_4969_;
                        v___y_4985_ = v___y_4971_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5029_ =
                            crate::leanh::lean_ctor_get(v___y_4970_, 13);
                        v_cls_5030_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
                        v___x_5050_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
                        v___x_5051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5029_,
                            v_options_5027_,
                            v___x_5050_,
                        );
                        if v___x_5051_ == 0 {
                            crate::leanh::lean_dec(v_hint_4965_);
                            crate::leanh::lean_dec(v_mod_4963_);
                            v___y_4984_ = v___y_4969_;
                            v___y_4985_ = v___y_4971_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5052_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
                            if v_isExporting_4975_ == 0 {
                                v___x_5061_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21;
                                v___y_5054_ = v___x_5061_;
                                state = 8;
                                continue;
                            } else {
                                v___x_5062_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22;
                                v___y_5054_ = v___x_5062_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4979_, 1);
                    crate::leanh::lean_dec(v_hint_4965_);
                    crate::leanh::lean_dec(v_mod_4963_);
                    v___x_5063_ = crate::leanh::lean_box(0);
                    v___x_5064_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5064_, 0, v___x_5063_);
                    return v___x_5064_;
                }
            }
            1 => {
                v___x_4986_ = lean_st_ref_take(v___y_4985_);
                v_toEnvExtension_4987_ = crate::leanh::lean_ctor_get(v___x_4980_, 0);
                v_env_4988_ = crate::leanh::lean_ctor_get(v___x_4986_, 0);
                v_nextMacroScope_4989_ = crate::leanh::lean_ctor_get(v___x_4986_, 1);
                v_ngen_4990_ = crate::leanh::lean_ctor_get(v___x_4986_, 2);
                v_auxDeclNGen_4991_ = crate::leanh::lean_ctor_get(v___x_4986_, 3);
                v_traceState_4992_ = crate::leanh::lean_ctor_get(v___x_4986_, 4);
                v_messages_4993_ = crate::leanh::lean_ctor_get(v___x_4986_, 6);
                v_infoState_4994_ = crate::leanh::lean_ctor_get(v___x_4986_, 7);
                v_snapshotTasks_4995_ = crate::leanh::lean_ctor_get(v___x_4986_, 8);
                v_isSharedCheck_5023_ = (!crate::leanh::lean_is_exclusive(v___x_4986_)) as u8;
                if v_isSharedCheck_5023_ == 0 {
                    v_unused_5024_ = crate::leanh::lean_ctor_get(v___x_4986_, 5);
                    crate::leanh::lean_dec(v_unused_5024_);
                    v___x_4997_ = v___x_4986_;
                    v_isShared_4998_ = v_isSharedCheck_5023_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4995_);
                    crate::leanh::lean_inc(v_infoState_4994_);
                    crate::leanh::lean_inc(v_messages_4993_);
                    crate::leanh::lean_inc(v_traceState_4992_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4991_);
                    crate::leanh::lean_inc(v_ngen_4990_);
                    crate::leanh::lean_inc(v_nextMacroScope_4989_);
                    crate::leanh::lean_inc(v_env_4988_);
                    crate::leanh::lean_dec(v___x_4986_);
                    v___x_4997_ = crate::leanh::lean_box(0);
                    v_isShared_4998_ = v_isSharedCheck_5023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4999_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4987_, 2);
                v___x_5000_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4980_,
                    v_env_4988_,
                    v_entry_4979_,
                    v_asyncMode_4999_,
                    v___x_4982_,
                );
                v___x_5001_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5);
                if v_isShared_4998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4997_, 5, v___x_5001_);
                    crate::leanh::lean_ctor_set(v___x_4997_, 0, v___x_5000_);
                    v___x_5003_ = v___x_4997_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5000_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_nextMacroScope_4989_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 2, v_ngen_4990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 3, v_auxDeclNGen_4991_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 4, v_traceState_4992_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 5, v___x_5001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 6, v_messages_4993_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 7, v_infoState_4994_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5022_, 8, v_snapshotTasks_4995_);
                    v___x_5003_ = v_reuseFailAlloc_5022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5004_ = lean_st_ref_set(v___y_4985_, v___x_5003_);
                v___x_5005_ = lean_st_ref_take(v___y_4984_);
                v_mctx_5006_ = crate::leanh::lean_ctor_get(v___x_5005_, 0);
                v_zetaDeltaFVarIds_5007_ = crate::leanh::lean_ctor_get(v___x_5005_, 2);
                v_postponed_5008_ = crate::leanh::lean_ctor_get(v___x_5005_, 3);
                v_diag_5009_ = crate::leanh::lean_ctor_get(v___x_5005_, 4);
                v_isSharedCheck_5020_ = (!crate::leanh::lean_is_exclusive(v___x_5005_)) as u8;
                if v_isSharedCheck_5020_ == 0 {
                    v_unused_5021_ = crate::leanh::lean_ctor_get(v___x_5005_, 1);
                    crate::leanh::lean_dec(v_unused_5021_);
                    v___x_5011_ = v___x_5005_;
                    v_isShared_5012_ = v_isSharedCheck_5020_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5009_);
                    crate::leanh::lean_inc(v_postponed_5008_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5007_);
                    crate::leanh::lean_inc(v_mctx_5006_);
                    crate::leanh::lean_dec(v___x_5005_);
                    v___x_5011_ = crate::leanh::lean_box(0);
                    v_isShared_5012_ = v_isSharedCheck_5020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5013_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6);
                if v_isShared_5012_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5011_, 1, v___x_5013_);
                    v___x_5015_ = v___x_5011_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5019_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_mctx_5006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_5013_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5019_,
                        2,
                        v_zetaDeltaFVarIds_5007_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 3, v_postponed_5008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5019_, 4, v_diag_5009_);
                    v___x_5015_ = v_reuseFailAlloc_5019_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5016_ = lean_st_ref_set(v___y_4984_, v___x_5015_);
                v___x_5017_ = crate::leanh::lean_box(0);
                v___x_5018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5018_, 0, v___x_5017_);
                return v___x_5018_;
            }
            6 => {
                v___x_5034_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5034_, 0, v___y_5032_);
                crate::leanh::lean_ctor_set(v___x_5034_, 1, v___y_5033_);
                v___x_5035_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_5030_, v___x_5034_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
                if crate::leanh::lean_obj_tag(v___x_5035_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5035_, 1);
                    v___y_4984_ = v___y_4969_;
                    v___y_4985_ = v___y_4971_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4979_, 1);
                    return v___x_5035_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_5038_);
                v___x_5039_ = l_Lean_stringToMessageData(v___y_5038_);
                v___x_5040_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5040_, 0, v___y_5037_);
                crate::leanh::lean_ctor_set(v___x_5040_, 1, v___x_5039_);
                v___x_5041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
                v___x_5042_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5042_, 0, v___x_5040_);
                crate::leanh::lean_ctor_set(v___x_5042_, 1, v___x_5041_);
                v___x_5043_ = l_Lean_MessageData_ofName(v_mod_4963_);
                v___x_5044_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5044_, 0, v___x_5042_);
                crate::leanh::lean_ctor_set(v___x_5044_, 1, v___x_5043_);
                v___x_5045_ = l_Lean_Name_isAnonymous(v_hint_4965_);
                if v___x_5045_ == 0 {
                    v___x_5046_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
                    v___x_5047_ = l_Lean_MessageData_ofName(v_hint_4965_);
                    v___x_5048_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5048_, 0, v___x_5046_);
                    crate::leanh::lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                    v___y_5032_ = v___x_5044_;
                    v___y_5033_ = v___x_5048_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_4965_);
                    v___x_5049_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
                    v___y_5032_ = v___x_5044_;
                    v___y_5033_ = v___x_5049_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_5054_);
                v___x_5055_ = l_Lean_stringToMessageData(v___y_5054_);
                v___x_5056_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5056_, 0, v___x_5052_);
                crate::leanh::lean_ctor_set(v___x_5056_, 1, v___x_5055_);
                v___x_5057_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
                v___x_5058_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5058_, 0, v___x_5056_);
                crate::leanh::lean_ctor_set(v___x_5058_, 1, v___x_5057_);
                if v_isMeta_4964_ == 0 {
                    v___x_5059_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19;
                    v___y_5037_ = v___x_5058_;
                    v___y_5038_ = v___x_5059_;
                    state = 7;
                    continue;
                } else {
                    v___x_5060_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20;
                    v___y_5037_ = v___x_5058_;
                    v___y_5038_ = v___x_5060_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___boxed(
    mut v_mod_5065_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5066_: *mut crate::leanh::LeanObject,
    mut v_hint_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
    mut v___y_5074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_5075_: u8 = 0;
    let mut v_res_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5075_ = (crate::leanh::lean_unbox(v_isMeta_5066_) as u8);
    v_res_5076_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_5065_, v_isMeta_boxed_5075_, v_hint_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
    crate::leanh::lean_dec(v___y_5073_);
    crate::leanh::lean_dec_ref(v___y_5072_);
    crate::leanh::lean_dec(v___y_5071_);
    crate::leanh::lean_dec_ref(v___y_5070_);
    crate::leanh::lean_dec(v___y_5069_);
    crate::leanh::lean_dec_ref(v___y_5068_);
    return v_res_5076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(
    mut v___x_5077_: *mut crate::leanh::LeanObject,
    mut v_declName_5078_: *mut crate::leanh::LeanObject,
    mut v_as_5079_: *mut crate::leanh::LeanObject,
    mut v_sz_5080_: usize,
    mut v_i_5081_: usize,
    mut v_b_5082_: *mut crate::leanh::LeanObject,
    mut v___y_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
    mut v___y_5085_: *mut crate::leanh::LeanObject,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5090_: u8 = 0;
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: usize = 0;
    let mut v___x_5103_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5090_ = lean_usize_dec_lt(v_i_5081_, v_sz_5080_);
                if v___x_5090_ == 0 {
                    crate::leanh::lean_dec(v_declName_5078_);
                    v___x_5091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5091_, 0, v_b_5082_);
                    return v___x_5091_;
                } else {
                    v___x_5092_ = l_Lean_Environment_header(v___x_5077_);
                    v_modules_5093_ = crate::leanh::lean_ctor_get(v___x_5092_, 3);
                    crate::leanh::lean_inc_ref(v_modules_5093_);
                    crate::leanh::lean_dec_ref(v___x_5092_);
                    v___x_5094_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_5095_ = lean_array_uget_borrowed(v_as_5079_, v_i_5081_);
                    v___x_5096_ = lean_array_get(v___x_5094_, v_modules_5093_, v_a_5095_);
                    crate::leanh::lean_dec_ref(v_modules_5093_);
                    v_toImport_5097_ = crate::leanh::lean_ctor_get(v___x_5096_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_5097_);
                    crate::leanh::lean_dec(v___x_5096_);
                    v_module_5098_ = crate::leanh::lean_ctor_get(v_toImport_5097_, 0);
                    crate::leanh::lean_inc(v_module_5098_);
                    crate::leanh::lean_dec_ref(v_toImport_5097_);
                    v___x_5099_ = 0;
                    crate::leanh::lean_inc(v_declName_5078_);
                    v___x_5100_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_5098_, v___x_5099_, v_declName_5078_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
                    if crate::leanh::lean_obj_tag(v___x_5100_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5100_, 1);
                        v___x_5101_ = crate::leanh::lean_box(0);
                        v___x_5102_ = 1usize;
                        v___x_5103_ = lean_usize_add(v_i_5081_, v___x_5102_);
                        v_i_5081_ = v___x_5103_;
                        v_b_5082_ = v___x_5101_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_5078_);
                        return v___x_5100_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(
    mut v___x_5105_: *mut crate::leanh::LeanObject,
    mut v_declName_5106_: *mut crate::leanh::LeanObject,
    mut v_as_5107_: *mut crate::leanh::LeanObject,
    mut v_sz_5108_: *mut crate::leanh::LeanObject,
    mut v_i_5109_: *mut crate::leanh::LeanObject,
    mut v_b_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
    mut v___y_5114_: *mut crate::leanh::LeanObject,
    mut v___y_5115_: *mut crate::leanh::LeanObject,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
    mut v___y_5117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5118_: usize = 0;
    let mut v_i_boxed_5119_: usize = 0;
    let mut v_res_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5118_ = crate::leanh::lean_unbox_usize(v_sz_5108_);
    crate::leanh::lean_dec(v_sz_5108_);
    v_i_boxed_5119_ = crate::leanh::lean_unbox_usize(v_i_5109_);
    crate::leanh::lean_dec(v_i_5109_);
    v_res_5120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_5105_, v_declName_5106_, v_as_5107_, v_sz_boxed_5118_, v_i_boxed_5119_, v_b_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
    crate::leanh::lean_dec(v___y_5116_);
    crate::leanh::lean_dec_ref(v___y_5115_);
    crate::leanh::lean_dec(v___y_5114_);
    crate::leanh::lean_dec_ref(v___y_5113_);
    crate::leanh::lean_dec(v___y_5112_);
    crate::leanh::lean_dec_ref(v___y_5111_);
    crate::leanh::lean_dec_ref(v_as_5107_);
    crate::leanh::lean_dec_ref(v___x_5105_);
    return v_res_5120_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5123_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1;
    v___x_5124_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0;
    v___x_5125_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_5124_,
        v___x_5123_,
    );
    return v___x_5125_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(
    mut v_declName_5128_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5129_: u8,
    mut v___y_5130_: *mut crate::leanh::LeanObject,
    mut v___y_5131_: *mut crate::leanh::LeanObject,
    mut v___y_5132_: *mut crate::leanh::LeanObject,
    mut v___y_5133_: *mut crate::leanh::LeanObject,
    mut v___y_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5145_: usize = 0;
    let mut v___x_5146_: usize = 0;
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5154_: u8 = 0;
    let mut v_unused_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: u8 = 0;
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5167_: u8 = 0;
    let mut v_toImport_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: u8 = 0;
    let mut v___x_5179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5137_ = lean_st_ref_get(v___y_5135_);
                v_env_5141_ = crate::leanh::lean_ctor_get(v___x_5137_, 0);
                crate::leanh::lean_inc_ref(v_env_5141_);
                crate::leanh::lean_dec(v___x_5137_);
                v___x_5156_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5141_, v_declName_5128_);
                if crate::leanh::lean_obj_tag(v___x_5156_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_5141_);
                    crate::leanh::lean_dec(v_declName_5128_);
                    state = 1;
                    continue;
                } else {
                    v_val_5157_ = crate::leanh::lean_ctor_get(v___x_5156_, 0);
                    crate::leanh::lean_inc(v_val_5157_);
                    crate::leanh::lean_dec_ref_known(v___x_5156_, 1);
                    v___x_5158_ = l_Lean_Environment_header(v_env_5141_);
                    v_modules_5159_ = crate::leanh::lean_ctor_get(v___x_5158_, 3);
                    crate::leanh::lean_inc_ref(v_modules_5159_);
                    crate::leanh::lean_dec_ref(v___x_5158_);
                    v___x_5160_ = lean_array_get_size(v_modules_5159_);
                    v___x_5161_ = lean_nat_dec_lt(v_val_5157_, v___x_5160_);
                    if v___x_5161_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_5159_);
                        crate::leanh::lean_dec(v_val_5157_);
                        crate::leanh::lean_dec_ref(v_env_5141_);
                        crate::leanh::lean_dec(v_declName_5128_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5162_ = lean_st_ref_get(v___y_5135_);
                        v_env_5163_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
                        crate::leanh::lean_inc_ref(v_env_5163_);
                        crate::leanh::lean_dec(v___x_5162_);
                        v___x_5164_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
                        v___x_5165_ = lean_array_fget(v_modules_5159_, v_val_5157_);
                        crate::leanh::lean_dec(v_val_5157_);
                        crate::leanh::lean_dec_ref(v_modules_5159_);
                        if v_isMeta_5129_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_5163_);
                            v___y_5167_ = v_isMeta_5129_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_5128_);
                            v___x_5178_ = l_Lean_isMarkedMeta(v_env_5163_, v_declName_5128_);
                            if v___x_5178_ == 0 {
                                v___y_5167_ = v_isMeta_5129_;
                                state = 5;
                                continue;
                            } else {
                                v___x_5179_ = 0;
                                v___y_5167_ = v___x_5179_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5139_ = crate::leanh::lean_box(0);
                v___x_5140_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5140_, 0, v___x_5139_);
                return v___x_5140_;
            }
            2 => {
                v___x_5144_ = crate::leanh::lean_box(0);
                v_sz_5145_ = lean_array_size(v___y_5143_);
                v___x_5146_ = 0usize;
                v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_5141_, v_declName_5128_, v___y_5143_, v_sz_5145_, v___x_5146_, v___x_5144_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
                crate::leanh::lean_dec_ref(v___y_5143_);
                crate::leanh::lean_dec_ref(v_env_5141_);
                if crate::leanh::lean_obj_tag(v___x_5147_) == 0 {
                    v_isSharedCheck_5154_ = (!crate::leanh::lean_is_exclusive(v___x_5147_)) as u8;
                    if v_isSharedCheck_5154_ == 0 {
                        v_unused_5155_ = crate::leanh::lean_ctor_get(v___x_5147_, 0);
                        crate::leanh::lean_dec(v_unused_5155_);
                        v___x_5149_ = v___x_5147_;
                        v_isShared_5150_ = v_isSharedCheck_5154_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5147_);
                        v___x_5149_ = crate::leanh::lean_box(0);
                        v_isShared_5150_ = v_isSharedCheck_5154_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_5147_;
                }
            }
            3 => {
                if v_isShared_5150_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5149_, 0, v___x_5144_);
                    v___x_5152_ = v___x_5149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5153_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5144_);
                    v___x_5152_ = v_reuseFailAlloc_5153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5152_;
            }
            5 => {
                v_toImport_5168_ = crate::leanh::lean_ctor_get(v___x_5165_, 0);
                crate::leanh::lean_inc_ref(v_toImport_5168_);
                crate::leanh::lean_dec(v___x_5165_);
                v_module_5169_ = crate::leanh::lean_ctor_get(v_toImport_5168_, 0);
                crate::leanh::lean_inc(v_module_5169_);
                crate::leanh::lean_dec_ref(v_toImport_5168_);
                crate::leanh::lean_inc(v_declName_5128_);
                v___x_5170_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_5169_, v___y_5167_, v_declName_5128_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
                if crate::leanh::lean_obj_tag(v___x_5170_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5170_, 1);
                    v___x_5171_ = l_Lean_indirectModUseExt;
                    v___x_5172_ = crate::leanh::lean_box(1);
                    v___x_5173_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_5141_);
                    v___x_5174_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_5164_,
                        v___x_5171_,
                        v_env_5141_,
                        v___x_5172_,
                        v___x_5173_,
                    );
                    v___x_5175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_5174_, v_declName_5128_);
                    crate::leanh::lean_dec(v___x_5174_);
                    if crate::leanh::lean_obj_tag(v___x_5175_) == 0 {
                        v___x_5176_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3;
                        v___y_5143_ = v___x_5176_;
                        state = 2;
                        continue;
                    } else {
                        v_val_5177_ = crate::leanh::lean_ctor_get(v___x_5175_, 0);
                        crate::leanh::lean_inc(v_val_5177_);
                        crate::leanh::lean_dec_ref_known(v___x_5175_, 1);
                        v___y_5143_ = v_val_5177_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_5141_);
                    crate::leanh::lean_dec(v_declName_5128_);
                    return v___x_5170_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(
    mut v_declName_5180_: *mut crate::leanh::LeanObject,
    mut v_isMeta_5181_: *mut crate::leanh::LeanObject,
    mut v___y_5182_: *mut crate::leanh::LeanObject,
    mut v___y_5183_: *mut crate::leanh::LeanObject,
    mut v___y_5184_: *mut crate::leanh::LeanObject,
    mut v___y_5185_: *mut crate::leanh::LeanObject,
    mut v___y_5186_: *mut crate::leanh::LeanObject,
    mut v___y_5187_: *mut crate::leanh::LeanObject,
    mut v___y_5188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_5189_: u8 = 0;
    let mut v_res_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5189_ = (crate::leanh::lean_unbox(v_isMeta_5181_) as u8);
    v_res_5190_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_5180_, v_isMeta_boxed_5189_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
    crate::leanh::lean_dec(v___y_5187_);
    crate::leanh::lean_dec_ref(v___y_5186_);
    crate::leanh::lean_dec(v___y_5185_);
    crate::leanh::lean_dec_ref(v___y_5184_);
    crate::leanh::lean_dec(v___y_5183_);
    crate::leanh::lean_dec_ref(v___y_5182_);
    return v_res_5190_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(
    mut v_as_x27_5191_: *mut crate::leanh::LeanObject,
    mut v_b_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
    mut v___y_5195_: *mut crate::leanh::LeanObject,
    mut v___y_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5191_) == 0 {
                    v___x_5200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5200_, 0, v_b_5192_);
                    return v___x_5200_;
                } else {
                    v_head_5201_ = crate::leanh::lean_ctor_get(v_as_x27_5191_, 0);
                    v_tail_5202_ = crate::leanh::lean_ctor_get(v_as_x27_5191_, 1);
                    v___x_5203_ = 1;
                    crate::leanh::lean_inc(v_head_5201_);
                    v___x_5204_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_5201_, v___x_5203_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
                    if crate::leanh::lean_obj_tag(v___x_5204_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5204_, 1);
                        v___x_5205_ = crate::leanh::lean_box(0);
                        v_as_x27_5191_ = v_tail_5202_;
                        v_b_5192_ = v___x_5205_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5204_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg___boxed(
    mut v_as_x27_5207_: *mut crate::leanh::LeanObject,
    mut v_b_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
    mut v___y_5210_: *mut crate::leanh::LeanObject,
    mut v___y_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5216_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_5207_, v_b_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
    crate::leanh::lean_dec(v___y_5214_);
    crate::leanh::lean_dec_ref(v___y_5213_);
    crate::leanh::lean_dec(v___y_5212_);
    crate::leanh::lean_dec_ref(v___y_5211_);
    crate::leanh::lean_dec(v___y_5210_);
    crate::leanh::lean_dec_ref(v___y_5209_);
    crate::leanh::lean_dec(v_as_x27_5207_);
    return v_res_5216_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(
    mut v_env_5217_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5218_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5219_: *mut crate::leanh::LeanObject,
    mut v_n_5220_: *mut crate::leanh::LeanObject,
    mut v___y_5221_: *mut crate::leanh::LeanObject,
    mut v___y_5222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5223_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5217_,
        v_currNamespace_5218_,
        v_openDecls_5219_,
        v_n_5220_,
    );
    v___x_5224_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5224_, 0, v___x_5223_);
    crate::leanh::lean_ctor_set(v___x_5224_, 1, v___y_5222_);
    return v___x_5224_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(
    mut v_env_5225_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_5226_: *mut crate::leanh::LeanObject,
    mut v_openDecls_5227_: *mut crate::leanh::LeanObject,
    mut v_n_5228_: *mut crate::leanh::LeanObject,
    mut v___y_5229_: *mut crate::leanh::LeanObject,
    mut v___y_5230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5231_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_5225_, v_currNamespace_5226_, v_openDecls_5227_, v_n_5228_, v___y_5229_, v___y_5230_);
    crate::leanh::lean_dec_ref(v___y_5229_);
    return v_res_5231_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5232_ = crate::leanh::lean_box(1);
    v___x_5233_ = l_Lean_MessageData_ofFormat(v___x_5232_);
    return v___x_5233_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5237_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2;
    v___x_5238_ = l_Lean_MessageData_ofFormat(v___x_5237_);
    return v___x_5238_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(
    mut v_x_5239_: *mut crate::leanh::LeanObject,
    mut v_x_5240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5245_: u8 = 0;
    let mut v_before_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v_unused_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5240_) == 0 {
                    return v_x_5239_;
                } else {
                    v_head_5241_ = crate::leanh::lean_ctor_get(v_x_5240_, 0);
                    v_tail_5242_ = crate::leanh::lean_ctor_get(v_x_5240_, 1);
                    v_isSharedCheck_5264_ = (!crate::leanh::lean_is_exclusive(v_x_5240_)) as u8;
                    if v_isSharedCheck_5264_ == 0 {
                        v___x_5244_ = v_x_5240_;
                        v_isShared_5245_ = v_isSharedCheck_5264_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_5242_);
                        crate::leanh::lean_inc(v_head_5241_);
                        crate::leanh::lean_dec(v_x_5240_);
                        v___x_5244_ = crate::leanh::lean_box(0);
                        v_isShared_5245_ = v_isSharedCheck_5264_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5246_ = crate::leanh::lean_ctor_get(v_head_5241_, 0);
                v_isSharedCheck_5262_ = (!crate::leanh::lean_is_exclusive(v_head_5241_)) as u8;
                if v_isSharedCheck_5262_ == 0 {
                    v_unused_5263_ = crate::leanh::lean_ctor_get(v_head_5241_, 1);
                    crate::leanh::lean_dec(v_unused_5263_);
                    v___x_5248_ = v_head_5241_;
                    v_isShared_5249_ = v_isSharedCheck_5262_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_5246_);
                    crate::leanh::lean_dec(v_head_5241_);
                    v___x_5248_ = crate::leanh::lean_box(0);
                    v_isShared_5249_ = v_isSharedCheck_5262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5250_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
                if v_isShared_5249_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5248_, 7);
                    crate::leanh::lean_ctor_set(v___x_5248_, 1, v___x_5250_);
                    crate::leanh::lean_ctor_set(v___x_5248_, 0, v_x_5239_);
                    v___x_5252_ = v___x_5248_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_x_5239_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5261_, 1, v___x_5250_);
                    v___x_5252_ = v_reuseFailAlloc_5261_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
                if v_isShared_5245_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5244_, 7);
                    crate::leanh::lean_ctor_set(v___x_5244_, 1, v___x_5253_);
                    crate::leanh::lean_ctor_set(v___x_5244_, 0, v___x_5252_);
                    v___x_5255_ = v___x_5244_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5260_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 1, v___x_5253_);
                    v___x_5255_ = v_reuseFailAlloc_5260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5256_ = l_Lean_MessageData_ofSyntax(v_before_5246_);
                v___x_5257_ = l_Lean_indentD(v___x_5256_);
                v___x_5258_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5258_, 0, v___x_5255_);
                crate::leanh::lean_ctor_set(v___x_5258_, 1, v___x_5257_);
                v_x_5239_ = v___x_5258_;
                v_x_5240_ = v_tail_5242_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(
    mut v_opts_5265_: *mut crate::leanh::LeanObject,
    mut v_opt_5266_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_5267_ = crate::leanh::lean_ctor_get(v_opt_5266_, 0);
    v_defValue_5268_ = crate::leanh::lean_ctor_get(v_opt_5266_, 1);
    v_map_5269_ = crate::leanh::lean_ctor_get(v_opts_5265_, 0);
    v___x_5270_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5269_,
            v_name_5267_,
        );
    if crate::leanh::lean_obj_tag(v___x_5270_) == 0 {
        let mut v___x_5271_: u8 = 0;
        v___x_5271_ = (crate::leanh::lean_unbox(v_defValue_5268_) as u8);
        return v___x_5271_;
    } else {
        let mut v_val_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_5272_ = crate::leanh::lean_ctor_get(v___x_5270_, 0);
        crate::leanh::lean_inc(v_val_5272_);
        crate::leanh::lean_dec_ref_known(v___x_5270_, 1);
        if crate::leanh::lean_obj_tag(v_val_5272_) == 1 {
            let mut v_v_5273_: u8 = 0;
            v_v_5273_ = crate::leanh::lean_ctor_get_uint8(v_val_5272_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_5272_, 0);
            return v_v_5273_;
        } else {
            let mut v___x_5274_: u8 = 0;
            crate::leanh::lean_dec(v_val_5272_);
            v___x_5274_ = (crate::leanh::lean_unbox(v_defValue_5268_) as u8);
            return v___x_5274_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(
    mut v_opts_5275_: *mut crate::leanh::LeanObject,
    mut v_opt_5276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5277_: u8 = 0;
    let mut v_r_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5277_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_5275_, v_opt_5276_);
    crate::leanh::lean_dec_ref(v_opt_5276_);
    crate::leanh::lean_dec_ref(v_opts_5275_);
    v_r_5278_ = crate::leanh::lean_box((v_res_5277_) as usize);
    return v_r_5278_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5282_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1;
    v___x_5283_ = l_Lean_MessageData_ofFormat(v___x_5282_);
    return v___x_5283_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(
    mut v_msgData_5284_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5285_: *mut crate::leanh::LeanObject,
    mut v___y_5286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: u8 = 0;
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5309_: u8 = 0;
    let mut v_unused_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5288_ = crate::leanh::lean_ctor_get(v___y_5286_, 2);
                v___x_5289_ = l_Lean_Elab_pp_macroStack;
                v___x_5290_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_5288_, v___x_5289_);
                if v___x_5290_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_5285_);
                    v___x_5291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5291_, 0, v_msgData_5284_);
                    return v___x_5291_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_5285_) == 0 {
                        v___x_5292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5292_, 0, v_msgData_5284_);
                        return v___x_5292_;
                    } else {
                        v_head_5293_ = crate::leanh::lean_ctor_get(v_macroStack_5285_, 0);
                        crate::leanh::lean_inc(v_head_5293_);
                        v_after_5294_ = crate::leanh::lean_ctor_get(v_head_5293_, 1);
                        v_isSharedCheck_5309_ =
                            (!crate::leanh::lean_is_exclusive(v_head_5293_)) as u8;
                        if v_isSharedCheck_5309_ == 0 {
                            v_unused_5310_ = crate::leanh::lean_ctor_get(v_head_5293_, 0);
                            crate::leanh::lean_dec(v_unused_5310_);
                            v___x_5296_ = v_head_5293_;
                            v_isShared_5297_ = v_isSharedCheck_5309_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_5294_);
                            crate::leanh::lean_dec(v_head_5293_);
                            v___x_5296_ = crate::leanh::lean_box(0);
                            v_isShared_5297_ = v_isSharedCheck_5309_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5298_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
                if v_isShared_5297_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5296_, 7);
                    crate::leanh::lean_ctor_set(v___x_5296_, 1, v___x_5298_);
                    crate::leanh::lean_ctor_set(v___x_5296_, 0, v_msgData_5284_);
                    v___x_5300_ = v___x_5296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5308_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_msgData_5284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5308_, 1, v___x_5298_);
                    v___x_5300_ = v_reuseFailAlloc_5308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
                v___x_5302_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5302_, 0, v___x_5300_);
                crate::leanh::lean_ctor_set(v___x_5302_, 1, v___x_5301_);
                v___x_5303_ = l_Lean_MessageData_ofSyntax(v_after_5294_);
                v___x_5304_ = l_Lean_indentD(v___x_5303_);
                v_msgData_5305_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_5305_, 0, v___x_5302_);
                crate::leanh::lean_ctor_set(v_msgData_5305_, 1, v___x_5304_);
                v___x_5306_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_5305_, v_macroStack_5285_);
                v___x_5307_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5307_, 0, v___x_5306_);
                return v___x_5307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(
    mut v_msgData_5311_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_5311_, v_macroStack_5312_, v___y_5313_);
    crate::leanh::lean_dec_ref(v___y_5313_);
    return v_res_5315_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(
    mut v_msg_5316_: *mut crate::leanh::LeanObject,
    mut v___y_5317_: *mut crate::leanh::LeanObject,
    mut v___y_5318_: *mut crate::leanh::LeanObject,
    mut v___y_5319_: *mut crate::leanh::LeanObject,
    mut v___y_5320_: *mut crate::leanh::LeanObject,
    mut v___y_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5324_ = crate::leanh::lean_ctor_get(v___y_5321_, 5);
                v___x_5325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_5316_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
                v_a_5326_ = crate::leanh::lean_ctor_get(v___x_5325_, 0);
                crate::leanh::lean_inc(v_a_5326_);
                crate::leanh::lean_dec_ref(v___x_5325_);
                v_macroStack_5327_ = crate::leanh::lean_ctor_get(v___y_5317_, 1);
                v___x_5328_ = l_Lean_Elab_getBetterRef(v_ref_5324_, v_macroStack_5327_);
                crate::leanh::lean_inc(v_macroStack_5327_);
                v___x_5329_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_5326_, v_macroStack_5327_, v___y_5321_);
                v_a_5330_ = crate::leanh::lean_ctor_get(v___x_5329_, 0);
                v_isSharedCheck_5338_ = (!crate::leanh::lean_is_exclusive(v___x_5329_)) as u8;
                if v_isSharedCheck_5338_ == 0 {
                    v___x_5332_ = v___x_5329_;
                    v_isShared_5333_ = v_isSharedCheck_5338_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5330_);
                    crate::leanh::lean_dec(v___x_5329_);
                    v___x_5332_ = crate::leanh::lean_box(0);
                    v_isShared_5333_ = v_isSharedCheck_5338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5334_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5334_, 0, v___x_5328_);
                crate::leanh::lean_ctor_set(v___x_5334_, 1, v_a_5330_);
                if v_isShared_5333_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5332_, 1);
                    crate::leanh::lean_ctor_set(v___x_5332_, 0, v___x_5334_);
                    v___x_5336_ = v___x_5332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5334_);
                    v___x_5336_ = v_reuseFailAlloc_5337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg___boxed(
    mut v_msg_5339_: *mut crate::leanh::LeanObject,
    mut v___y_5340_: *mut crate::leanh::LeanObject,
    mut v___y_5341_: *mut crate::leanh::LeanObject,
    mut v___y_5342_: *mut crate::leanh::LeanObject,
    mut v___y_5343_: *mut crate::leanh::LeanObject,
    mut v___y_5344_: *mut crate::leanh::LeanObject,
    mut v___y_5345_: *mut crate::leanh::LeanObject,
    mut v___y_5346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5347_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
    crate::leanh::lean_dec(v___y_5345_);
    crate::leanh::lean_dec_ref(v___y_5344_);
    crate::leanh::lean_dec(v___y_5343_);
    crate::leanh::lean_dec_ref(v___y_5342_);
    crate::leanh::lean_dec(v___y_5341_);
    crate::leanh::lean_dec_ref(v___y_5340_);
    return v_res_5347_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(
    mut v_ref_5348_: *mut crate::leanh::LeanObject,
    mut v_msg_5349_: *mut crate::leanh::LeanObject,
    mut v___y_5350_: *mut crate::leanh::LeanObject,
    mut v___y_5351_: *mut crate::leanh::LeanObject,
    mut v___y_5352_: *mut crate::leanh::LeanObject,
    mut v___y_5353_: *mut crate::leanh::LeanObject,
    mut v___y_5354_: *mut crate::leanh::LeanObject,
    mut v___y_5355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5369_: u8 = 0;
    let mut v_cancelTk_x3f_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5371_: u8 = 0;
    let mut v_inheritedTraceOptions_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_5357_ = crate::leanh::lean_ctor_get(v___y_5354_, 0);
    v_fileMap_5358_ = crate::leanh::lean_ctor_get(v___y_5354_, 1);
    v_options_5359_ = crate::leanh::lean_ctor_get(v___y_5354_, 2);
    v_currRecDepth_5360_ = crate::leanh::lean_ctor_get(v___y_5354_, 3);
    v_maxRecDepth_5361_ = crate::leanh::lean_ctor_get(v___y_5354_, 4);
    v_ref_5362_ = crate::leanh::lean_ctor_get(v___y_5354_, 5);
    v_currNamespace_5363_ = crate::leanh::lean_ctor_get(v___y_5354_, 6);
    v_openDecls_5364_ = crate::leanh::lean_ctor_get(v___y_5354_, 7);
    v_initHeartbeats_5365_ = crate::leanh::lean_ctor_get(v___y_5354_, 8);
    v_maxHeartbeats_5366_ = crate::leanh::lean_ctor_get(v___y_5354_, 9);
    v_quotContext_5367_ = crate::leanh::lean_ctor_get(v___y_5354_, 10);
    v_currMacroScope_5368_ = crate::leanh::lean_ctor_get(v___y_5354_, 11);
    v_diag_5369_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5354_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5370_ = crate::leanh::lean_ctor_get(v___y_5354_, 12);
    v_suppressElabErrors_5371_ = crate::leanh::lean_ctor_get_uint8(
        v___y_5354_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5372_ = crate::leanh::lean_ctor_get(v___y_5354_, 13);
    v_ref_5373_ = l_Lean_replaceRef(v_ref_5348_, v_ref_5362_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_5372_);
    crate::leanh::lean_inc(v_cancelTk_x3f_5370_);
    crate::leanh::lean_inc(v_currMacroScope_5368_);
    crate::leanh::lean_inc(v_quotContext_5367_);
    crate::leanh::lean_inc(v_maxHeartbeats_5366_);
    crate::leanh::lean_inc(v_initHeartbeats_5365_);
    crate::leanh::lean_inc(v_openDecls_5364_);
    crate::leanh::lean_inc(v_currNamespace_5363_);
    crate::leanh::lean_inc(v_maxRecDepth_5361_);
    crate::leanh::lean_inc(v_currRecDepth_5360_);
    crate::leanh::lean_inc_ref(v_options_5359_);
    crate::leanh::lean_inc_ref(v_fileMap_5358_);
    crate::leanh::lean_inc_ref(v_fileName_5357_);
    v___x_5374_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_5374_, 0, v_fileName_5357_);
    crate::leanh::lean_ctor_set(v___x_5374_, 1, v_fileMap_5358_);
    crate::leanh::lean_ctor_set(v___x_5374_, 2, v_options_5359_);
    crate::leanh::lean_ctor_set(v___x_5374_, 3, v_currRecDepth_5360_);
    crate::leanh::lean_ctor_set(v___x_5374_, 4, v_maxRecDepth_5361_);
    crate::leanh::lean_ctor_set(v___x_5374_, 5, v_ref_5373_);
    crate::leanh::lean_ctor_set(v___x_5374_, 6, v_currNamespace_5363_);
    crate::leanh::lean_ctor_set(v___x_5374_, 7, v_openDecls_5364_);
    crate::leanh::lean_ctor_set(v___x_5374_, 8, v_initHeartbeats_5365_);
    crate::leanh::lean_ctor_set(v___x_5374_, 9, v_maxHeartbeats_5366_);
    crate::leanh::lean_ctor_set(v___x_5374_, 10, v_quotContext_5367_);
    crate::leanh::lean_ctor_set(v___x_5374_, 11, v_currMacroScope_5368_);
    crate::leanh::lean_ctor_set(v___x_5374_, 12, v_cancelTk_x3f_5370_);
    crate::leanh::lean_ctor_set(v___x_5374_, 13, v_inheritedTraceOptions_5372_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_5374_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_5369_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_5374_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5371_,
    );
    v___x_5375_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___x_5374_, v___y_5355_);
    crate::leanh::lean_dec_ref_known(v___x_5374_, 14);
    return v___x_5375_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(
    mut v_ref_5376_: *mut crate::leanh::LeanObject,
    mut v_msg_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5385_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_5376_, v_msg_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
    crate::leanh::lean_dec(v___y_5383_);
    crate::leanh::lean_dec_ref(v___y_5382_);
    crate::leanh::lean_dec(v___y_5381_);
    crate::leanh::lean_dec_ref(v___y_5380_);
    crate::leanh::lean_dec(v___y_5379_);
    crate::leanh::lean_dec_ref(v___y_5378_);
    crate::leanh::lean_dec(v_ref_5376_);
    return v_res_5385_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(
    mut v_x_5387_: *mut crate::leanh::LeanObject,
    mut v___y_5388_: *mut crate::leanh::LeanObject,
    mut v___y_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5435_: u8 = 0;
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5447_: u8 = 0;
    let mut v_unused_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5452_: u8 = 0;
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut v_reuseFailAlloc_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_unused_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v_a_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: u8 = 0;
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5395_ = lean_st_ref_get(v___y_5393_);
                v_env_5396_ = crate::leanh::lean_ctor_get(v___x_5395_, 0);
                crate::leanh::lean_inc_ref_n(v_env_5396_, 4);
                crate::leanh::lean_dec(v___x_5395_);
                v_options_5397_ = crate::leanh::lean_ctor_get(v___y_5392_, 2);
                v_currRecDepth_5398_ = crate::leanh::lean_ctor_get(v___y_5392_, 3);
                v_maxRecDepth_5399_ = crate::leanh::lean_ctor_get(v___y_5392_, 4);
                v_ref_5400_ = crate::leanh::lean_ctor_get(v___y_5392_, 5);
                v_currNamespace_5401_ = crate::leanh::lean_ctor_get(v___y_5392_, 6);
                v_openDecls_5402_ = crate::leanh::lean_ctor_get(v___y_5392_, 7);
                v_quotContext_5403_ = crate::leanh::lean_ctor_get(v___y_5392_, 10);
                v_currMacroScope_5404_ = crate::leanh::lean_ctor_get(v___y_5392_, 11);
                v___x_5405_ = lean_st_ref_get(v___y_5393_);
                v_nextMacroScope_5406_ = crate::leanh::lean_ctor_get(v___x_5405_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_5406_);
                crate::leanh::lean_dec(v___x_5405_);
                v___f_5407_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_5407_, 0, v_env_5396_);
                v___f_5408_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_5408_, 0, v_env_5396_);
                crate::leanh::lean_inc_n(v_openDecls_5402_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_5401_, 3);
                v___f_5409_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___f_5409_, 0, v_env_5396_);
                crate::leanh::lean_closure_set(v___f_5409_, 1, v_currNamespace_5401_);
                crate::leanh::lean_closure_set(v___f_5409_, 2, v_openDecls_5402_);
                v___f_5410_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_5410_, 0, v_currNamespace_5401_);
                crate::leanh::lean_inc_ref(v_options_5397_);
                v___f_5411_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                crate::leanh::lean_closure_set(v___f_5411_, 0, v_env_5396_);
                crate::leanh::lean_closure_set(v___f_5411_, 1, v_options_5397_);
                crate::leanh::lean_closure_set(v___f_5411_, 2, v_currNamespace_5401_);
                crate::leanh::lean_closure_set(v___f_5411_, 3, v_openDecls_5402_);
                v_methods_5412_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_methods_5412_, 0, v___f_5407_);
                crate::leanh::lean_ctor_set(v_methods_5412_, 1, v___f_5410_);
                crate::leanh::lean_ctor_set(v_methods_5412_, 2, v___f_5408_);
                crate::leanh::lean_ctor_set(v_methods_5412_, 3, v___f_5409_);
                crate::leanh::lean_ctor_set(v_methods_5412_, 4, v___f_5411_);
                crate::leanh::lean_inc(v_ref_5400_);
                crate::leanh::lean_inc(v_maxRecDepth_5399_);
                crate::leanh::lean_inc(v_currRecDepth_5398_);
                crate::leanh::lean_inc(v_currMacroScope_5404_);
                crate::leanh::lean_inc(v_quotContext_5403_);
                v___x_5413_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5413_, 0, v_methods_5412_);
                crate::leanh::lean_ctor_set(v___x_5413_, 1, v_quotContext_5403_);
                crate::leanh::lean_ctor_set(v___x_5413_, 2, v_currMacroScope_5404_);
                crate::leanh::lean_ctor_set(v___x_5413_, 3, v_currRecDepth_5398_);
                crate::leanh::lean_ctor_set(v___x_5413_, 4, v_maxRecDepth_5399_);
                crate::leanh::lean_ctor_set(v___x_5413_, 5, v_ref_5400_);
                v___x_5414_ = crate::leanh::lean_box(0);
                v___x_5415_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5415_, 0, v_nextMacroScope_5406_);
                crate::leanh::lean_ctor_set(v___x_5415_, 1, v___x_5414_);
                crate::leanh::lean_ctor_set(v___x_5415_, 2, v___x_5414_);
                v___x_5416_ = crate::leanh::lean_apply_2(v_x_5387_, v___x_5413_, v___x_5415_);
                if crate::leanh::lean_obj_tag(v___x_5416_) == 0 {
                    v_a_5417_ = crate::leanh::lean_ctor_get(v___x_5416_, 1);
                    crate::leanh::lean_inc(v_a_5417_);
                    v_a_5418_ = crate::leanh::lean_ctor_get(v___x_5416_, 0);
                    crate::leanh::lean_inc(v_a_5418_);
                    crate::leanh::lean_dec_ref_known(v___x_5416_, 2);
                    v_macroScope_5419_ = crate::leanh::lean_ctor_get(v_a_5417_, 0);
                    crate::leanh::lean_inc(v_macroScope_5419_);
                    v_traceMsgs_5420_ = crate::leanh::lean_ctor_get(v_a_5417_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_5420_);
                    v_expandedMacroDecls_5421_ = crate::leanh::lean_ctor_get(v_a_5417_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_5421_);
                    crate::leanh::lean_dec(v_a_5417_);
                    v___x_5422_ = crate::leanh::lean_box(0);
                    v___x_5423_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_5421_, v___x_5422_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_5421_);
                    if crate::leanh::lean_obj_tag(v___x_5423_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5423_, 1);
                        v___x_5424_ = lean_st_ref_take(v___y_5393_);
                        v_env_5425_ = crate::leanh::lean_ctor_get(v___x_5424_, 0);
                        v_ngen_5426_ = crate::leanh::lean_ctor_get(v___x_5424_, 2);
                        v_auxDeclNGen_5427_ = crate::leanh::lean_ctor_get(v___x_5424_, 3);
                        v_traceState_5428_ = crate::leanh::lean_ctor_get(v___x_5424_, 4);
                        v_cache_5429_ = crate::leanh::lean_ctor_get(v___x_5424_, 5);
                        v_messages_5430_ = crate::leanh::lean_ctor_get(v___x_5424_, 6);
                        v_infoState_5431_ = crate::leanh::lean_ctor_get(v___x_5424_, 7);
                        v_snapshotTasks_5432_ = crate::leanh::lean_ctor_get(v___x_5424_, 8);
                        v_isSharedCheck_5458_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5424_)) as u8;
                        if v_isSharedCheck_5458_ == 0 {
                            v_unused_5459_ = crate::leanh::lean_ctor_get(v___x_5424_, 1);
                            crate::leanh::lean_dec(v_unused_5459_);
                            v___x_5434_ = v___x_5424_;
                            v_isShared_5435_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_5432_);
                            crate::leanh::lean_inc(v_infoState_5431_);
                            crate::leanh::lean_inc(v_messages_5430_);
                            crate::leanh::lean_inc(v_cache_5429_);
                            crate::leanh::lean_inc(v_traceState_5428_);
                            crate::leanh::lean_inc(v_auxDeclNGen_5427_);
                            crate::leanh::lean_inc(v_ngen_5426_);
                            crate::leanh::lean_inc(v_env_5425_);
                            crate::leanh::lean_dec(v___x_5424_);
                            v___x_5434_ = crate::leanh::lean_box(0);
                            v_isShared_5435_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_5420_);
                        crate::leanh::lean_dec(v_macroScope_5419_);
                        crate::leanh::lean_dec(v_a_5418_);
                        v_a_5460_ = crate::leanh::lean_ctor_get(v___x_5423_, 0);
                        v_isSharedCheck_5467_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5423_)) as u8;
                        if v_isSharedCheck_5467_ == 0 {
                            v___x_5462_ = v___x_5423_;
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5460_);
                            crate::leanh::lean_dec(v___x_5423_);
                            v___x_5462_ = crate::leanh::lean_box(0);
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_5468_ = crate::leanh::lean_ctor_get(v___x_5416_, 0);
                    crate::leanh::lean_inc(v_a_5468_);
                    crate::leanh::lean_dec_ref_known(v___x_5416_, 2);
                    if crate::leanh::lean_obj_tag(v_a_5468_) == 0 {
                        v_a_5469_ = crate::leanh::lean_ctor_get(v_a_5468_, 0);
                        crate::leanh::lean_inc(v_a_5469_);
                        v_a_5470_ = crate::leanh::lean_ctor_get(v_a_5468_, 1);
                        crate::leanh::lean_inc_ref(v_a_5470_);
                        crate::leanh::lean_dec_ref_known(v_a_5468_, 2);
                        v___x_5471_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0;
                        v___x_5472_ = lean_string_dec_eq(v_a_5470_, v___x_5471_);
                        if v___x_5472_ == 0 {
                            v___x_5473_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5473_, 0, v_a_5470_);
                            v___x_5474_ = l_Lean_MessageData_ofFormat(v___x_5473_);
                            v___x_5475_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_5469_, v___x_5474_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
                            crate::leanh::lean_dec(v_a_5469_);
                            return v___x_5475_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_5470_);
                            v___x_5476_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_a_5469_);
                            return v___x_5476_;
                        }
                    } else {
                        v___x_5477_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
                        return v___x_5477_;
                    }
                }
            }
            1 => {
                if v_isShared_5435_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5434_, 1, v_macroScope_5419_);
                    v___x_5437_ = v___x_5434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_env_5425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_macroScope_5419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_ngen_5426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_auxDeclNGen_5427_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 4, v_traceState_5428_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 5, v_cache_5429_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 6, v_messages_5430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 7, v_infoState_5431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5457_, 8, v_snapshotTasks_5432_);
                    v___x_5437_ = v_reuseFailAlloc_5457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5438_ = lean_st_ref_set(v___y_5393_, v___x_5437_);
                v___x_5439_ = l_List_reverse___redArg(v_traceMsgs_5420_);
                v___x_5440_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_5439_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
                if crate::leanh::lean_obj_tag(v___x_5440_) == 0 {
                    v_isSharedCheck_5447_ = (!crate::leanh::lean_is_exclusive(v___x_5440_)) as u8;
                    if v_isSharedCheck_5447_ == 0 {
                        v_unused_5448_ = crate::leanh::lean_ctor_get(v___x_5440_, 0);
                        crate::leanh::lean_dec(v_unused_5448_);
                        v___x_5442_ = v___x_5440_;
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5440_);
                        v___x_5442_ = crate::leanh::lean_box(0);
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5418_);
                    v_a_5449_ = crate::leanh::lean_ctor_get(v___x_5440_, 0);
                    v_isSharedCheck_5456_ = (!crate::leanh::lean_is_exclusive(v___x_5440_)) as u8;
                    if v_isSharedCheck_5456_ == 0 {
                        v___x_5451_ = v___x_5440_;
                        v_isShared_5452_ = v_isSharedCheck_5456_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5449_);
                        crate::leanh::lean_dec(v___x_5440_);
                        v___x_5451_ = crate::leanh::lean_box(0);
                        v_isShared_5452_ = v_isSharedCheck_5456_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5443_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5442_, 0, v_a_5418_);
                    v___x_5445_ = v___x_5442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5446_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5418_);
                    v___x_5445_ = v_reuseFailAlloc_5446_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5445_;
            }
            5 => {
                if v_isShared_5452_ == 0 {
                    v___x_5454_ = v___x_5451_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5455_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_a_5449_);
                    v___x_5454_ = v_reuseFailAlloc_5455_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5454_;
            }
            7 => {
                if v_isShared_5463_ == 0 {
                    v___x_5465_ = v___x_5462_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___boxed(
    mut v_x_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5486_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
    crate::leanh::lean_dec(v___y_5484_);
    crate::leanh::lean_dec_ref(v___y_5483_);
    crate::leanh::lean_dec(v___y_5482_);
    crate::leanh::lean_dec_ref(v___y_5481_);
    crate::leanh::lean_dec(v___y_5480_);
    crate::leanh::lean_dec_ref(v___y_5479_);
    return v_res_5486_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(
    mut v_t_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5492_: u8 = 0;
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v_enabled_5508_: u8 = 0;
    let mut v_assignment_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trees_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5525_: u8 = 0;
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5490_ = lean_st_ref_get(v___y_5488_);
                v_infoState_5491_ = crate::leanh::lean_ctor_get(v___x_5490_, 7);
                crate::leanh::lean_inc_ref(v_infoState_5491_);
                crate::leanh::lean_dec(v___x_5490_);
                v_enabled_5492_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5491_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                crate::leanh::lean_dec_ref(v_infoState_5491_);
                if v_enabled_5492_ == 0 {
                    crate::leanh::lean_dec_ref(v_t_5487_);
                    v___x_5493_ = crate::leanh::lean_box(0);
                    v___x_5494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5494_, 0, v___x_5493_);
                    return v___x_5494_;
                } else {
                    v___x_5495_ = lean_st_ref_take(v___y_5488_);
                    v_infoState_5496_ = crate::leanh::lean_ctor_get(v___x_5495_, 7);
                    v_env_5497_ = crate::leanh::lean_ctor_get(v___x_5495_, 0);
                    v_nextMacroScope_5498_ = crate::leanh::lean_ctor_get(v___x_5495_, 1);
                    v_ngen_5499_ = crate::leanh::lean_ctor_get(v___x_5495_, 2);
                    v_auxDeclNGen_5500_ = crate::leanh::lean_ctor_get(v___x_5495_, 3);
                    v_traceState_5501_ = crate::leanh::lean_ctor_get(v___x_5495_, 4);
                    v_cache_5502_ = crate::leanh::lean_ctor_get(v___x_5495_, 5);
                    v_messages_5503_ = crate::leanh::lean_ctor_get(v___x_5495_, 6);
                    v_snapshotTasks_5504_ = crate::leanh::lean_ctor_get(v___x_5495_, 8);
                    v_isSharedCheck_5526_ = (!crate::leanh::lean_is_exclusive(v___x_5495_)) as u8;
                    if v_isSharedCheck_5526_ == 0 {
                        v___x_5506_ = v___x_5495_;
                        v_isShared_5507_ = v_isSharedCheck_5526_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_5504_);
                        crate::leanh::lean_inc(v_infoState_5496_);
                        crate::leanh::lean_inc(v_messages_5503_);
                        crate::leanh::lean_inc(v_cache_5502_);
                        crate::leanh::lean_inc(v_traceState_5501_);
                        crate::leanh::lean_inc(v_auxDeclNGen_5500_);
                        crate::leanh::lean_inc(v_ngen_5499_);
                        crate::leanh::lean_inc(v_nextMacroScope_5498_);
                        crate::leanh::lean_inc(v_env_5497_);
                        crate::leanh::lean_dec(v___x_5495_);
                        v___x_5506_ = crate::leanh::lean_box(0);
                        v_isShared_5507_ = v_isSharedCheck_5526_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_5508_ = crate::leanh::lean_ctor_get_uint8(
                    v_infoState_5496_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_assignment_5509_ = crate::leanh::lean_ctor_get(v_infoState_5496_, 0);
                v_lazyAssignment_5510_ = crate::leanh::lean_ctor_get(v_infoState_5496_, 1);
                v_trees_5511_ = crate::leanh::lean_ctor_get(v_infoState_5496_, 2);
                v_isSharedCheck_5525_ = (!crate::leanh::lean_is_exclusive(v_infoState_5496_)) as u8;
                if v_isSharedCheck_5525_ == 0 {
                    v___x_5513_ = v_infoState_5496_;
                    v_isShared_5514_ = v_isSharedCheck_5525_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_trees_5511_);
                    crate::leanh::lean_inc(v_lazyAssignment_5510_);
                    crate::leanh::lean_inc(v_assignment_5509_);
                    crate::leanh::lean_dec(v_infoState_5496_);
                    v___x_5513_ = crate::leanh::lean_box(0);
                    v_isShared_5514_ = v_isSharedCheck_5525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5515_ = l_Lean_PersistentArray_push___redArg(v_trees_5511_, v_t_5487_);
                if v_isShared_5514_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5513_, 2, v___x_5515_);
                    v___x_5517_ = v___x_5513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_assignment_5509_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_lazyAssignment_5510_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 2, v___x_5515_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5524_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                        v_enabled_5508_,
                    );
                    v___x_5517_ = v_reuseFailAlloc_5524_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5507_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5506_, 7, v___x_5517_);
                    v___x_5519_ = v___x_5506_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5523_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_env_5497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_nextMacroScope_5498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_ngen_5499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_auxDeclNGen_5500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_traceState_5501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 5, v_cache_5502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 6, v_messages_5503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 7, v___x_5517_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5523_, 8, v_snapshotTasks_5504_);
                    v___x_5519_ = v_reuseFailAlloc_5523_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5520_ = lean_st_ref_set(v___y_5488_, v___x_5519_);
                v___x_5521_ = crate::leanh::lean_box(0);
                v___x_5522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                return v___x_5522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(
    mut v_t_5527_: *mut crate::leanh::LeanObject,
    mut v___y_5528_: *mut crate::leanh::LeanObject,
    mut v___y_5529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5530_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_5527_, v___y_5528_);
    crate::leanh::lean_dec(v___y_5528_);
    return v_res_5530_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5531_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5532_ = lean_mk_empty_array_with_capacity(v___x_5531_);
    v___x_5533_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5533_, 0, v___x_5532_);
    return v___x_5533_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5534_: usize = 0;
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5534_ = 5usize;
    v___x_5535_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5536_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_5537_ = lean_mk_empty_array_with_capacity(v___x_5536_);
    v___x_5538_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
    v___x_5539_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_5539_, 0, v___x_5538_);
    crate::leanh::lean_ctor_set(v___x_5539_, 1, v___x_5537_);
    crate::leanh::lean_ctor_set(v___x_5539_, 2, v___x_5535_);
    crate::leanh::lean_ctor_set(v___x_5539_, 3, v___x_5535_);
    crate::leanh::lean_ctor_set_usize(v___x_5539_, 4, v___x_5534_);
    return v___x_5539_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(
    mut v_t_5540_: *mut crate::leanh::LeanObject,
    mut v___y_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_enabled_5550_: u8 = 0;
    v___x_5548_ = lean_st_ref_get(v___y_5546_);
    v_infoState_5549_ = crate::leanh::lean_ctor_get(v___x_5548_, 7);
    crate::leanh::lean_inc_ref(v_infoState_5549_);
    crate::leanh::lean_dec(v___x_5548_);
    v_enabled_5550_ = crate::leanh::lean_ctor_get_uint8(
        v_infoState_5549_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
    );
    crate::leanh::lean_dec_ref(v_infoState_5549_);
    if v_enabled_5550_ == 0 {
        let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_t_5540_);
        v___x_5551_ = crate::leanh::lean_box(0);
        v___x_5552_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5552_, 0, v___x_5551_);
        return v___x_5552_;
    } else {
        let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5553_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
        v___x_5554_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5554_, 0, v_t_5540_);
        crate::leanh::lean_ctor_set(v___x_5554_, 1, v___x_5553_);
        v___x_5555_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_5554_, v___y_5546_);
        return v___x_5555_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(
    mut v_t_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
    mut v___y_5563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5564_ =
        l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(
            v_t_5556_,
            v___y_5557_,
            v___y_5558_,
            v___y_5559_,
            v___y_5560_,
            v___y_5561_,
            v___y_5562_,
        );
    crate::leanh::lean_dec(v___y_5562_);
    crate::leanh::lean_dec_ref(v___y_5561_);
    crate::leanh::lean_dec(v___y_5560_);
    crate::leanh::lean_dec_ref(v___y_5559_);
    crate::leanh::lean_dec(v___y_5558_);
    crate::leanh::lean_dec_ref(v___y_5557_);
    return v_res_5564_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(
    mut v_info_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
    mut v___y_5569_: *mut crate::leanh::LeanObject,
    mut v___y_5570_: *mut crate::leanh::LeanObject,
    mut v___y_5571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5573_ = crate::leanh::lean_alloc_ctor(8, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5573_, 0, v_info_5565_);
    v___x_5574_ =
        l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(
            v___x_5573_,
            v___y_5566_,
            v___y_5567_,
            v___y_5568_,
            v___y_5569_,
            v___y_5570_,
            v___y_5571_,
        );
    return v___x_5574_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1___boxed(
    mut v_info_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
    mut v___y_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
    mut v___y_5580_: *mut crate::leanh::LeanObject,
    mut v___y_5581_: *mut crate::leanh::LeanObject,
    mut v___y_5582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
    crate::leanh::lean_dec(v___y_5581_);
    crate::leanh::lean_dec_ref(v___y_5580_);
    crate::leanh::lean_dec(v___y_5579_);
    crate::leanh::lean_dec_ref(v___y_5578_);
    crate::leanh::lean_dec(v___y_5577_);
    crate::leanh::lean_dec_ref(v___y_5576_);
    return v_res_5583_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(
    mut v___y_5591_: u8,
    mut v_suppressElabErrors_5592_: u8,
    mut v_x_5593_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_5593_) == 1 {
        let mut v_pre_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_5594_ = crate::leanh::lean_ctor_get(v_x_5593_, 0);
        match crate::leanh::lean_obj_tag(v_pre_5594_) {
            1 => {
                let mut v_pre_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_5595_ = crate::leanh::lean_ctor_get(v_pre_5594_, 0);
                match crate::leanh::lean_obj_tag(v_pre_5595_) {
                    0 => {
                        let mut v_str_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_5599_: u8 = 0;
                        v_str_5596_ = crate::leanh::lean_ctor_get(v_x_5593_, 1);
                        v_str_5597_ = crate::leanh::lean_ctor_get(v_pre_5594_, 1);
                        v___x_5598_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0;
                        v___x_5599_ = lean_string_dec_eq(v_str_5597_, v___x_5598_);
                        if v___x_5599_ == 0 {
                            let mut v___x_5600_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5601_: u8 = 0;
                            v___x_5600_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1;
                            v___x_5601_ = lean_string_dec_eq(v_str_5597_, v___x_5600_);
                            if v___x_5601_ == 0 {
                                return v___y_5591_;
                            } else {
                                let mut v___x_5602_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5603_: u8 = 0;
                                v___x_5602_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2;
                                v___x_5603_ = lean_string_dec_eq(v_str_5596_, v___x_5602_);
                                if v___x_5603_ == 0 {
                                    return v___y_5591_;
                                } else {
                                    return v_suppressElabErrors_5592_;
                                }
                            }
                        } else {
                            let mut v___x_5604_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5605_: u8 = 0;
                            v___x_5604_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3;
                            v___x_5605_ = lean_string_dec_eq(v_str_5596_, v___x_5604_);
                            if v___x_5605_ == 0 {
                                return v___y_5591_;
                            } else {
                                return v_suppressElabErrors_5592_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_5606_ = crate::leanh::lean_ctor_get(v_pre_5595_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_5606_) == 0 {
                            let mut v_str_5607_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5608_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_5609_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5610_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5611_: u8 = 0;
                            v_str_5607_ = crate::leanh::lean_ctor_get(v_x_5593_, 1);
                            v_str_5608_ = crate::leanh::lean_ctor_get(v_pre_5594_, 1);
                            v_str_5609_ = crate::leanh::lean_ctor_get(v_pre_5595_, 1);
                            v___x_5610_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4;
                            v___x_5611_ = lean_string_dec_eq(v_str_5609_, v___x_5610_);
                            if v___x_5611_ == 0 {
                                return v___y_5591_;
                            } else {
                                let mut v___x_5612_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_5613_: u8 = 0;
                                v___x_5612_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5;
                                v___x_5613_ = lean_string_dec_eq(v_str_5608_, v___x_5612_);
                                if v___x_5613_ == 0 {
                                    return v___y_5591_;
                                } else {
                                    let mut v___x_5614_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_5615_: u8 = 0;
                                    v___x_5614_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6;
                                    v___x_5615_ = lean_string_dec_eq(v_str_5607_, v___x_5614_);
                                    if v___x_5615_ == 0 {
                                        return v___y_5591_;
                                    } else {
                                        return v_suppressElabErrors_5592_;
                                    }
                                }
                            }
                        } else {
                            return v___y_5591_;
                        }
                    }
                    _ => {
                        return v___y_5591_;
                    }
                }
            }
            0 => {
                let mut v_str_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5618_: u8 = 0;
                v_str_5616_ = crate::leanh::lean_ctor_get(v_x_5593_, 1);
                v___x_5617_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0;
                v___x_5618_ = lean_string_dec_eq(v_str_5616_, v___x_5617_);
                if v___x_5618_ == 0 {
                    return v___y_5591_;
                } else {
                    return v_suppressElabErrors_5592_;
                }
            }
            _ => {
                return v___y_5591_;
            }
        }
    } else {
        return v___y_5591_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed(
    mut v___y_5619_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_5620_: *mut crate::leanh::LeanObject,
    mut v_x_5621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_21547__boxed_5622_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5623_: u8 = 0;
    let mut v_res_5624_: u8 = 0;
    let mut v_r_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_21547__boxed_5622_ = (crate::leanh::lean_unbox(v___y_5619_) as u8);
    v_suppressElabErrors_boxed_5623_ = (crate::leanh::lean_unbox(v_suppressElabErrors_5620_) as u8);
    v_res_5624_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v___y_21547__boxed_5622_, v_suppressElabErrors_boxed_5623_, v_x_5621_);
    crate::leanh::lean_dec(v_x_5621_);
    v_r_5625_ = crate::leanh::lean_box((v_res_5624_) as usize);
    return v_r_5625_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(
    mut v_ref_5626_: *mut crate::leanh::LeanObject,
    mut v_msgData_5627_: *mut crate::leanh::LeanObject,
    mut v_severity_5628_: u8,
    mut v_isSilent_5629_: u8,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5641_: u8 = 0;
    let mut v___y_5642_: u8 = 0;
    let mut v___y_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5670_: u8 = 0;
    let mut v___y_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5676_: u8 = 0;
    let mut v___y_5677_: u8 = 0;
    let mut v___y_5678_: u8 = 0;
    let mut v___y_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5685_: u8 = 0;
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5695_: u8 = 0;
    let mut v___y_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5701_: u8 = 0;
    let mut v___y_5702_: u8 = 0;
    let mut v___y_5703_: u8 = 0;
    let mut v___y_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5712_: u8 = 0;
    let mut v___y_5713_: u8 = 0;
    let mut v___y_5714_: u8 = 0;
    let mut v_ref_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: u8 = 0;
    let mut v___y_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5724_: u8 = 0;
    let mut v___y_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5726_: u8 = 0;
    let mut v___y_5727_: u8 = 0;
    let mut v___y_5729_: u8 = 0;
    let mut v_fileName_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5734_: u8 = 0;
    let mut v___x_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5744_: u8 = 0;
    let mut v___x_5745_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5719_ = 2;
                v___x_5744_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5628_, v___x_5719_);
                if v___x_5744_ == 0 {
                    v___y_5729_ = v___x_5744_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_5627_);
                    v___x_5745_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5627_);
                    v___y_5729_ = v___x_5745_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5645_ = lean_st_ref_take(v___y_5644_);
                v_currNamespace_5646_ = crate::leanh::lean_ctor_get(v___y_5643_, 6);
                v_openDecls_5647_ = crate::leanh::lean_ctor_get(v___y_5643_, 7);
                v_env_5648_ = crate::leanh::lean_ctor_get(v___x_5645_, 0);
                v_nextMacroScope_5649_ = crate::leanh::lean_ctor_get(v___x_5645_, 1);
                v_ngen_5650_ = crate::leanh::lean_ctor_get(v___x_5645_, 2);
                v_auxDeclNGen_5651_ = crate::leanh::lean_ctor_get(v___x_5645_, 3);
                v_traceState_5652_ = crate::leanh::lean_ctor_get(v___x_5645_, 4);
                v_cache_5653_ = crate::leanh::lean_ctor_get(v___x_5645_, 5);
                v_messages_5654_ = crate::leanh::lean_ctor_get(v___x_5645_, 6);
                v_infoState_5655_ = crate::leanh::lean_ctor_get(v___x_5645_, 7);
                v_snapshotTasks_5656_ = crate::leanh::lean_ctor_get(v___x_5645_, 8);
                v_isSharedCheck_5670_ = (!crate::leanh::lean_is_exclusive(v___x_5645_)) as u8;
                if v_isSharedCheck_5670_ == 0 {
                    v___x_5658_ = v___x_5645_;
                    v_isShared_5659_ = v_isSharedCheck_5670_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_5656_);
                    crate::leanh::lean_inc(v_infoState_5655_);
                    crate::leanh::lean_inc(v_messages_5654_);
                    crate::leanh::lean_inc(v_cache_5653_);
                    crate::leanh::lean_inc(v_traceState_5652_);
                    crate::leanh::lean_inc(v_auxDeclNGen_5651_);
                    crate::leanh::lean_inc(v_ngen_5650_);
                    crate::leanh::lean_inc(v_nextMacroScope_5649_);
                    crate::leanh::lean_inc(v_env_5648_);
                    crate::leanh::lean_dec(v___x_5645_);
                    v___x_5658_ = crate::leanh::lean_box(0);
                    v_isShared_5659_ = v_isSharedCheck_5670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_5647_);
                crate::leanh::lean_inc(v_currNamespace_5646_);
                v___x_5660_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5660_, 0, v_currNamespace_5646_);
                crate::leanh::lean_ctor_set(v___x_5660_, 1, v_openDecls_5647_);
                v___x_5661_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5661_, 0, v___x_5660_);
                crate::leanh::lean_ctor_set(v___x_5661_, 1, v___y_5638_);
                crate::leanh::lean_inc_ref(v___y_5639_);
                crate::leanh::lean_inc_ref(v___y_5637_);
                v___x_5662_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_5662_, 0, v___y_5637_);
                crate::leanh::lean_ctor_set(v___x_5662_, 1, v___y_5640_);
                crate::leanh::lean_ctor_set(v___x_5662_, 2, v___y_5636_);
                crate::leanh::lean_ctor_set(v___x_5662_, 3, v___y_5639_);
                crate::leanh::lean_ctor_set(v___x_5662_, 4, v___x_5661_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5662_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_5642_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5662_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_5641_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5662_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5629_,
                );
                v___x_5663_ = l_Lean_MessageLog_add(v___x_5662_, v_messages_5654_);
                if v_isShared_5659_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5658_, 6, v___x_5663_);
                    v___x_5665_ = v___x_5658_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_env_5648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_nextMacroScope_5649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 2, v_ngen_5650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 3, v_auxDeclNGen_5651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 4, v_traceState_5652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 5, v_cache_5653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 6, v___x_5663_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 7, v_infoState_5655_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5669_, 8, v_snapshotTasks_5656_);
                    v___x_5665_ = v_reuseFailAlloc_5669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5666_ = lean_st_ref_set(v___y_5644_, v___x_5665_);
                v___x_5667_ = crate::leanh::lean_box(0);
                v___x_5668_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5668_, 0, v___x_5667_);
                return v___x_5668_;
            }
            4 => {
                v___x_5680_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5627_,
                    );
                v___x_5681_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_5680_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_);
                v_a_5682_ = crate::leanh::lean_ctor_get(v___x_5681_, 0);
                v_isSharedCheck_5695_ = (!crate::leanh::lean_is_exclusive(v___x_5681_)) as u8;
                if v_isSharedCheck_5695_ == 0 {
                    v___x_5684_ = v___x_5681_;
                    v_isShared_5685_ = v_isSharedCheck_5695_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5682_);
                    crate::leanh::lean_dec(v___x_5681_);
                    v___x_5684_ = crate::leanh::lean_box(0);
                    v_isShared_5685_ = v_isSharedCheck_5695_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_5673_, 2);
                v___x_5686_ = l_Lean_FileMap_toPosition(v___y_5673_, v___y_5674_);
                crate::leanh::lean_dec(v___y_5674_);
                v___x_5687_ = l_Lean_FileMap_toPosition(v___y_5673_, v___y_5679_);
                crate::leanh::lean_dec(v___y_5679_);
                v___x_5688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5688_, 0, v___x_5687_);
                v___x_5689_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                if v___y_5676_ == 0 {
                    crate::leanh::lean_del_object(v___x_5684_);
                    crate::leanh::lean_dec_ref(v___y_5672_);
                    v___y_5636_ = v___x_5688_;
                    v___y_5637_ = v___y_5675_;
                    v___y_5638_ = v_a_5682_;
                    v___y_5639_ = v___x_5689_;
                    v___y_5640_ = v___x_5686_;
                    v___y_5641_ = v___y_5677_;
                    v___y_5642_ = v___y_5678_;
                    v___y_5643_ = v___y_5632_;
                    v___y_5644_ = v___y_5633_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5682_);
                    v___x_5690_ = l_Lean_MessageData_hasTag(v___y_5672_, v_a_5682_);
                    if v___x_5690_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5688_, 1);
                        crate::leanh::lean_dec_ref(v___x_5686_);
                        crate::leanh::lean_dec(v_a_5682_);
                        v___x_5691_ = crate::leanh::lean_box(0);
                        if v_isShared_5685_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5684_, 0, v___x_5691_);
                            v___x_5693_ = v___x_5684_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5694_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5691_);
                            v___x_5693_ = v_reuseFailAlloc_5694_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5684_);
                        v___y_5636_ = v___x_5688_;
                        v___y_5637_ = v___y_5675_;
                        v___y_5638_ = v_a_5682_;
                        v___y_5639_ = v___x_5689_;
                        v___y_5640_ = v___x_5686_;
                        v___y_5641_ = v___y_5677_;
                        v___y_5642_ = v___y_5678_;
                        v___y_5643_ = v___y_5632_;
                        v___y_5644_ = v___y_5633_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5693_;
            }
            7 => {
                v___x_5705_ = l_Lean_Syntax_getTailPos_x3f(v___y_5698_, v___y_5703_);
                crate::leanh::lean_dec(v___y_5698_);
                if crate::leanh::lean_obj_tag(v___x_5705_) == 0 {
                    crate::leanh::lean_inc(v___y_5704_);
                    v___y_5672_ = v___y_5697_;
                    v___y_5673_ = v___y_5699_;
                    v___y_5674_ = v___y_5704_;
                    v___y_5675_ = v___y_5700_;
                    v___y_5676_ = v___y_5701_;
                    v___y_5677_ = v___y_5702_;
                    v___y_5678_ = v___y_5703_;
                    v___y_5679_ = v___y_5704_;
                    state = 4;
                    continue;
                } else {
                    v_val_5706_ = crate::leanh::lean_ctor_get(v___x_5705_, 0);
                    crate::leanh::lean_inc(v_val_5706_);
                    crate::leanh::lean_dec_ref_known(v___x_5705_, 1);
                    v___y_5672_ = v___y_5697_;
                    v___y_5673_ = v___y_5699_;
                    v___y_5674_ = v___y_5704_;
                    v___y_5675_ = v___y_5700_;
                    v___y_5676_ = v___y_5701_;
                    v___y_5677_ = v___y_5702_;
                    v___y_5678_ = v___y_5703_;
                    v___y_5679_ = v_val_5706_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_5715_ = l_Lean_replaceRef(v_ref_5626_, v___y_5711_);
                v___x_5716_ = l_Lean_Syntax_getPos_x3f(v_ref_5715_, v___y_5713_);
                if crate::leanh::lean_obj_tag(v___x_5716_) == 0 {
                    v___x_5717_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_5697_ = v___y_5708_;
                    v___y_5698_ = v_ref_5715_;
                    v___y_5699_ = v___y_5709_;
                    v___y_5700_ = v___y_5710_;
                    v___y_5701_ = v___y_5712_;
                    v___y_5702_ = v___y_5714_;
                    v___y_5703_ = v___y_5713_;
                    v___y_5704_ = v___x_5717_;
                    state = 7;
                    continue;
                } else {
                    v_val_5718_ = crate::leanh::lean_ctor_get(v___x_5716_, 0);
                    crate::leanh::lean_inc(v_val_5718_);
                    crate::leanh::lean_dec_ref_known(v___x_5716_, 1);
                    v___y_5697_ = v___y_5708_;
                    v___y_5698_ = v_ref_5715_;
                    v___y_5699_ = v___y_5709_;
                    v___y_5700_ = v___y_5710_;
                    v___y_5701_ = v___y_5712_;
                    v___y_5702_ = v___y_5714_;
                    v___y_5703_ = v___y_5713_;
                    v___y_5704_ = v_val_5718_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_5727_ == 0 {
                    v___y_5708_ = v___y_5725_;
                    v___y_5709_ = v___y_5721_;
                    v___y_5710_ = v___y_5722_;
                    v___y_5711_ = v___y_5723_;
                    v___y_5712_ = v___y_5724_;
                    v___y_5713_ = v___y_5726_;
                    v___y_5714_ = v_severity_5628_;
                    state = 8;
                    continue;
                } else {
                    v___y_5708_ = v___y_5725_;
                    v___y_5709_ = v___y_5721_;
                    v___y_5710_ = v___y_5722_;
                    v___y_5711_ = v___y_5723_;
                    v___y_5712_ = v___y_5724_;
                    v___y_5713_ = v___y_5726_;
                    v___y_5714_ = v___x_5719_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_5729_ == 0 {
                    v_fileName_5730_ = crate::leanh::lean_ctor_get(v___y_5632_, 0);
                    v_fileMap_5731_ = crate::leanh::lean_ctor_get(v___y_5632_, 1);
                    v_options_5732_ = crate::leanh::lean_ctor_get(v___y_5632_, 2);
                    v_ref_5733_ = crate::leanh::lean_ctor_get(v___y_5632_, 5);
                    v_suppressElabErrors_5734_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_5632_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5735_ = crate::leanh::lean_box((v___y_5729_) as usize);
                    v___x_5736_ = crate::leanh::lean_box((v_suppressElabErrors_5734_) as usize);
                    v___f_5737_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_5737_, 0, v___x_5735_);
                    crate::leanh::lean_closure_set(v___f_5737_, 1, v___x_5736_);
                    v___x_5738_ = 1;
                    v___x_5739_ = l_Lean_instBEqMessageSeverity_beq(v_severity_5628_, v___x_5738_);
                    if v___x_5739_ == 0 {
                        v___y_5721_ = v_fileMap_5731_;
                        v___y_5722_ = v_fileName_5730_;
                        v___y_5723_ = v_ref_5733_;
                        v___y_5724_ = v_suppressElabErrors_5734_;
                        v___y_5725_ = v___f_5737_;
                        v___y_5726_ = v___y_5729_;
                        v___y_5727_ = v___x_5739_;
                        state = 9;
                        continue;
                    } else {
                        v___x_5740_ = l_Lean_warningAsError;
                        v___x_5741_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_5732_, v___x_5740_);
                        v___y_5721_ = v_fileMap_5731_;
                        v___y_5722_ = v_fileName_5730_;
                        v___y_5723_ = v_ref_5733_;
                        v___y_5724_ = v_suppressElabErrors_5734_;
                        v___y_5725_ = v___f_5737_;
                        v___y_5726_ = v___y_5729_;
                        v___y_5727_ = v___x_5741_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_5627_);
                    v___x_5742_ = crate::leanh::lean_box(0);
                    v___x_5743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5743_, 0, v___x_5742_);
                    return v___x_5743_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(
    mut v_ref_5746_: *mut crate::leanh::LeanObject,
    mut v_msgData_5747_: *mut crate::leanh::LeanObject,
    mut v_severity_5748_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5749_: *mut crate::leanh::LeanObject,
    mut v___y_5750_: *mut crate::leanh::LeanObject,
    mut v___y_5751_: *mut crate::leanh::LeanObject,
    mut v___y_5752_: *mut crate::leanh::LeanObject,
    mut v___y_5753_: *mut crate::leanh::LeanObject,
    mut v___y_5754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5755_: u8 = 0;
    let mut v_isSilent_boxed_5756_: u8 = 0;
    let mut v_res_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5755_ = (crate::leanh::lean_unbox(v_severity_5748_) as u8);
    v_isSilent_boxed_5756_ = (crate::leanh::lean_unbox(v_isSilent_5749_) as u8);
    v_res_5757_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_5746_, v_msgData_5747_, v_severity_boxed_5755_, v_isSilent_boxed_5756_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
    crate::leanh::lean_dec(v___y_5753_);
    crate::leanh::lean_dec_ref(v___y_5752_);
    crate::leanh::lean_dec(v___y_5751_);
    crate::leanh::lean_dec_ref(v___y_5750_);
    crate::leanh::lean_dec(v_ref_5746_);
    return v_res_5757_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(
    mut v_ref_5758_: *mut crate::leanh::LeanObject,
    mut v_msgData_5759_: *mut crate::leanh::LeanObject,
    mut v___y_5760_: *mut crate::leanh::LeanObject,
    mut v___y_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5767_ = 2;
    v___x_5768_ = 0;
    v___x_5769_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_5758_, v_msgData_5759_, v___x_5767_, v___x_5768_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
    return v___x_5769_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(
    mut v_ref_5770_: *mut crate::leanh::LeanObject,
    mut v_msgData_5771_: *mut crate::leanh::LeanObject,
    mut v___y_5772_: *mut crate::leanh::LeanObject,
    mut v___y_5773_: *mut crate::leanh::LeanObject,
    mut v___y_5774_: *mut crate::leanh::LeanObject,
    mut v___y_5775_: *mut crate::leanh::LeanObject,
    mut v___y_5776_: *mut crate::leanh::LeanObject,
    mut v___y_5777_: *mut crate::leanh::LeanObject,
    mut v___y_5778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5779_ =
        l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(
            v_ref_5770_,
            v_msgData_5771_,
            v___y_5772_,
            v___y_5773_,
            v___y_5774_,
            v___y_5775_,
            v___y_5776_,
            v___y_5777_,
        );
    crate::leanh::lean_dec(v___y_5777_);
    crate::leanh::lean_dec_ref(v___y_5776_);
    crate::leanh::lean_dec(v___y_5775_);
    crate::leanh::lean_dec_ref(v___y_5774_);
    crate::leanh::lean_dec(v___y_5773_);
    crate::leanh::lean_dec_ref(v___y_5772_);
    crate::leanh::lean_dec(v_ref_5770_);
    return v_res_5779_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(
    mut v_ref_5780_: *mut crate::leanh::LeanObject,
    mut v_msgData_5781_: *mut crate::leanh::LeanObject,
    mut v___y_5782_: *mut crate::leanh::LeanObject,
    mut v___y_5783_: *mut crate::leanh::LeanObject,
    mut v___y_5784_: *mut crate::leanh::LeanObject,
    mut v___y_5785_: *mut crate::leanh::LeanObject,
    mut v___y_5786_: *mut crate::leanh::LeanObject,
    mut v___y_5787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5789_: u8 = 0;
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5789_ = 1;
    v___x_5790_ = 0;
    v___x_5791_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_5780_, v_msgData_5781_, v___x_5789_, v___x_5790_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
    return v___x_5791_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(
    mut v_ref_5792_: *mut crate::leanh::LeanObject,
    mut v_msgData_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
    mut v___y_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5801_ =
        l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(
            v_ref_5792_,
            v_msgData_5793_,
            v___y_5794_,
            v___y_5795_,
            v___y_5796_,
            v___y_5797_,
            v___y_5798_,
            v___y_5799_,
        );
    crate::leanh::lean_dec(v___y_5799_);
    crate::leanh::lean_dec_ref(v___y_5798_);
    crate::leanh::lean_dec(v___y_5797_);
    crate::leanh::lean_dec_ref(v___y_5796_);
    crate::leanh::lean_dec(v___y_5795_);
    crate::leanh::lean_dec_ref(v___y_5794_);
    crate::leanh::lean_dec(v_ref_5792_);
    return v_res_5801_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5803_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0;
    v___x_5804_ = l_Lean_stringToMessageData(v___x_5803_);
    return v___x_5804_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
    v___x_5807_ = l_Lean_stringToMessageData(v___x_5806_);
    return v___x_5807_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5809_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
    v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5812_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
    v___x_5813_ = l_Lean_stringToMessageData(v___x_5812_);
    return v___x_5813_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5815_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5818_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5821_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5824_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5827_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(
    mut v_stx_5829_: *mut crate::leanh::LeanObject,
    mut v_expType_x3f_5830_: *mut crate::leanh::LeanObject,
    mut v_a_5831_: *mut crate::leanh::LeanObject,
    mut v_a_5832_: *mut crate::leanh::LeanObject,
    mut v_a_5833_: *mut crate::leanh::LeanObject,
    mut v_a_5834_: *mut crate::leanh::LeanObject,
    mut v_a_5835_: *mut crate::leanh::LeanObject,
    mut v_a_5836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5839_: u8 = 0;
    let mut v___y_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5853_: u8 = 0;
    let mut v___x_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v___y_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5861_: u8 = 0;
    let mut v___y_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_partialId_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_metadata_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_removedVersion_x3f_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5902_: u8 = 0;
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v___x_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5920_: u8 = 0;
    let mut v_reuseFailAlloc_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5922_: u8 = 0;
    let mut v_unused_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: u8 = 0;
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5960_: u8 = 0;
    let mut v___x_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: u8 = 0;
    let mut v___x_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: u8 = 0;
    let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: u8 = 0;
    let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5985_: u8 = 0;
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: u8 = 0;
    let mut v___x_5989_: u8 = 0;
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6007_: u8 = 0;
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6011_: u8 = 0;
    let mut v_reuseFailAlloc_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5977_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
                crate::leanh::lean_inc(v_stx_5829_);
                v___x_5978_ = l_Lean_Syntax_getKind(v_stx_5829_);
                v___x_5979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_5977_, v___x_5978_);
                crate::leanh::lean_dec(v___x_5978_);
                if crate::leanh::lean_obj_tag(v___x_5979_) == 1 {
                    v_val_5980_ = crate::leanh::lean_ctor_get(v___x_5979_, 0);
                    crate::leanh::lean_inc(v_val_5980_);
                    crate::leanh::lean_dec_ref_known(v___x_5979_, 1);
                    v_fst_5981_ = crate::leanh::lean_ctor_get(v_val_5980_, 0);
                    v_snd_5982_ = crate::leanh::lean_ctor_get(v_val_5980_, 1);
                    v_isSharedCheck_6013_ = (!crate::leanh::lean_is_exclusive(v_val_5980_)) as u8;
                    if v_isSharedCheck_6013_ == 0 {
                        v___x_5984_ = v_val_5980_;
                        v_isShared_5985_ = v_isSharedCheck_6013_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5982_);
                        crate::leanh::lean_inc(v_fst_5981_);
                        crate::leanh::lean_dec(v_val_5980_);
                        v___x_5984_ = crate::leanh::lean_box(0);
                        v_isShared_5985_ = v_isSharedCheck_6013_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5979_);
                    v___y_5967_ = v_a_5831_;
                    v___y_5968_ = v_a_5832_;
                    v___y_5969_ = v_a_5833_;
                    v___y_5970_ = v_a_5834_;
                    v___y_5971_ = v_a_5835_;
                    v___y_5972_ = v_a_5836_;
                    state = 14;
                    continue;
                }
            }
            1 => {
                v___x_5846_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_5846_, 0, v_stx_5829_);
                v___x_5847_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_5846_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_);
                if crate::leanh::lean_obj_tag(v___x_5847_) == 0 {
                    v_a_5848_ = crate::leanh::lean_ctor_get(v___x_5847_, 0);
                    crate::leanh::lean_inc(v_a_5848_);
                    crate::leanh::lean_dec_ref_known(v___x_5847_, 1);
                    v___x_5849_ = l_Lean_Elab_Term_elabTerm(
                        v_a_5848_,
                        v_expType_x3f_5830_,
                        v___y_5839_,
                        v___y_5839_,
                        v___y_5840_,
                        v___y_5841_,
                        v___y_5842_,
                        v___y_5843_,
                        v___y_5844_,
                        v___y_5845_,
                    );
                    return v___x_5849_;
                } else {
                    crate::leanh::lean_dec(v_expType_x3f_5830_);
                    v_a_5850_ = crate::leanh::lean_ctor_get(v___x_5847_, 0);
                    v_isSharedCheck_5857_ = (!crate::leanh::lean_is_exclusive(v___x_5847_)) as u8;
                    if v_isSharedCheck_5857_ == 0 {
                        v___x_5852_ = v___x_5847_;
                        v_isShared_5853_ = v_isSharedCheck_5857_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5850_);
                        crate::leanh::lean_dec(v___x_5847_);
                        v___x_5852_ = crate::leanh::lean_box(0);
                        v_isShared_5853_ = v_isSharedCheck_5857_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5853_ == 0 {
                    v___x_5855_ = v___x_5852_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_a_5850_);
                    v___x_5855_ = v_reuseFailAlloc_5856_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5855_;
            }
            4 => {
                v___x_5868_ = l_Lean_Syntax_getNumArgs(v___y_5867_);
                v___x_5869_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5870_ = lean_nat_sub(v___x_5868_, v___x_5869_);
                crate::leanh::lean_dec(v___x_5868_);
                v_partialId_5871_ = l_Lean_Syntax_getArg(v___y_5867_, v___x_5870_);
                crate::leanh::lean_dec(v___x_5870_);
                v___x_5872_ = crate::leanh::lean_alloc_ctor(6, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5872_, 0, v___y_5867_);
                crate::leanh::lean_ctor_set(v___x_5872_, 1, v_partialId_5871_);
                v___x_5873_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_5872_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                v_isSharedCheck_5922_ = (!crate::leanh::lean_is_exclusive(v___x_5873_)) as u8;
                if v_isSharedCheck_5922_ == 0 {
                    v_unused_5923_ = crate::leanh::lean_ctor_get(v___x_5873_, 0);
                    crate::leanh::lean_dec(v_unused_5923_);
                    v___x_5875_ = v___x_5873_;
                    v_isShared_5876_ = v_isSharedCheck_5922_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5873_);
                    v___x_5875_ = crate::leanh::lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5922_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5877_ = l_Lean_Syntax_getId(v___y_5862_);
                v___x_5878_ = lean_erase_macro_scopes(v___x_5877_);
                crate::leanh::lean_inc(v___x_5878_);
                crate::leanh::lean_inc(v___y_5862_);
                v___x_5879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5879_, 0, v___y_5862_);
                crate::leanh::lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                if v_isShared_5876_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5875_, 6);
                    crate::leanh::lean_ctor_set(v___x_5875_, 0, v___x_5879_);
                    v___x_5881_ = v___x_5875_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5921_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5879_);
                    v___x_5881_ = v_reuseFailAlloc_5921_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5882_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_5881_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                crate::leanh::lean_dec_ref(v___x_5882_);
                v___x_5883_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_5878_, v___y_5859_);
                v_a_5884_ = crate::leanh::lean_ctor_get(v___x_5883_, 0);
                crate::leanh::lean_inc(v_a_5884_);
                crate::leanh::lean_dec_ref(v___x_5883_);
                if crate::leanh::lean_obj_tag(v_a_5884_) == 1 {
                    v_val_5885_ = crate::leanh::lean_ctor_get(v_a_5884_, 0);
                    crate::leanh::lean_inc(v_val_5885_);
                    crate::leanh::lean_dec_ref_known(v_a_5884_, 1);
                    v_metadata_5886_ = crate::leanh::lean_ctor_get(v_val_5885_, 1);
                    crate::leanh::lean_inc_ref(v_metadata_5886_);
                    crate::leanh::lean_dec(v_val_5885_);
                    v_removedVersion_x3f_5887_ = crate::leanh::lean_ctor_get(v_metadata_5886_, 2);
                    crate::leanh::lean_inc(v_removedVersion_x3f_5887_);
                    crate::leanh::lean_dec_ref(v_metadata_5886_);
                    if crate::leanh::lean_obj_tag(v_removedVersion_x3f_5887_) == 1 {
                        v_val_5888_ = crate::leanh::lean_ctor_get(v_removedVersion_x3f_5887_, 0);
                        crate::leanh::lean_inc(v_val_5888_);
                        crate::leanh::lean_dec_ref_known(v_removedVersion_x3f_5887_, 1);
                        v___x_5889_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once
                            ),
                            _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1,
                        );
                        v___x_5890_ = l_Lean_MessageData_ofName(v___x_5878_);
                        v___x_5891_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5891_, 0, v___x_5889_);
                        crate::leanh::lean_ctor_set(v___x_5891_, 1, v___x_5890_);
                        v___x_5892_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once
                            ),
                            _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3,
                        );
                        v___x_5893_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5893_, 0, v___x_5891_);
                        crate::leanh::lean_ctor_set(v___x_5893_, 1, v___x_5892_);
                        v___x_5894_ = l_Lean_stringToMessageData(v_val_5888_);
                        v___x_5895_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5895_, 0, v___x_5893_);
                        crate::leanh::lean_ctor_set(v___x_5895_, 1, v___x_5894_);
                        v___x_5896_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once
                            ),
                            _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5,
                        );
                        v___x_5897_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5897_, 0, v___x_5895_);
                        crate::leanh::lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                        v___x_5898_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_5862_, v___x_5897_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                        crate::leanh::lean_dec(v___y_5862_);
                        if crate::leanh::lean_obj_tag(v___x_5898_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5898_, 1);
                            v___y_5839_ = v___y_5861_;
                            v___y_5840_ = v___y_5865_;
                            v___y_5841_ = v___y_5863_;
                            v___y_5842_ = v___y_5860_;
                            v___y_5843_ = v___y_5864_;
                            v___y_5844_ = v___y_5866_;
                            v___y_5845_ = v___y_5859_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_expType_x3f_5830_);
                            crate::leanh::lean_dec(v_stx_5829_);
                            v_a_5899_ = crate::leanh::lean_ctor_get(v___x_5898_, 0);
                            v_isSharedCheck_5906_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5898_)) as u8;
                            if v_isSharedCheck_5906_ == 0 {
                                v___x_5901_ = v___x_5898_;
                                v_isShared_5902_ = v_isSharedCheck_5906_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5899_);
                                crate::leanh::lean_dec(v___x_5898_);
                                v___x_5901_ = crate::leanh::lean_box(0);
                                v_isShared_5902_ = v_isSharedCheck_5906_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_removedVersion_x3f_5887_);
                        crate::leanh::lean_dec(v___x_5878_);
                        crate::leanh::lean_dec(v___y_5862_);
                        v___y_5839_ = v___y_5861_;
                        v___y_5840_ = v___y_5865_;
                        v___y_5841_ = v___y_5863_;
                        v___y_5842_ = v___y_5860_;
                        v___y_5843_ = v___y_5864_;
                        v___y_5844_ = v___y_5866_;
                        v___y_5845_ = v___y_5859_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5884_);
                    v___x_5907_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once
                        ),
                        _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7,
                    );
                    v___x_5908_ = l_Lean_MessageData_ofName(v___x_5878_);
                    v___x_5909_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5909_, 0, v___x_5907_);
                    crate::leanh::lean_ctor_set(v___x_5909_, 1, v___x_5908_);
                    v___x_5910_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once
                        ),
                        _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9,
                    );
                    v___x_5911_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5911_, 0, v___x_5909_);
                    crate::leanh::lean_ctor_set(v___x_5911_, 1, v___x_5910_);
                    v___x_5912_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_5862_, v___x_5911_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                    crate::leanh::lean_dec(v___y_5862_);
                    if crate::leanh::lean_obj_tag(v___x_5912_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5912_, 1);
                        v___y_5839_ = v___y_5861_;
                        v___y_5840_ = v___y_5865_;
                        v___y_5841_ = v___y_5863_;
                        v___y_5842_ = v___y_5860_;
                        v___y_5843_ = v___y_5864_;
                        v___y_5844_ = v___y_5866_;
                        v___y_5845_ = v___y_5859_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_expType_x3f_5830_);
                        crate::leanh::lean_dec(v_stx_5829_);
                        v_a_5913_ = crate::leanh::lean_ctor_get(v___x_5912_, 0);
                        v_isSharedCheck_5920_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5912_)) as u8;
                        if v_isSharedCheck_5920_ == 0 {
                            v___x_5915_ = v___x_5912_;
                            v_isShared_5916_ = v_isSharedCheck_5920_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5913_);
                            crate::leanh::lean_dec(v___x_5912_);
                            v___x_5915_ = crate::leanh::lean_box(0);
                            v_isShared_5916_ = v_isSharedCheck_5920_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            7 => {
                if v_isShared_5902_ == 0 {
                    v___x_5904_ = v___x_5901_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5905_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5904_;
            }
            9 => {
                if v_isShared_5916_ == 0 {
                    v___x_5918_ = v___x_5915_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
                    v___x_5918_ = v_reuseFailAlloc_5919_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5918_;
            }
            11 => {
                v___x_5933_ = l_Lean_Syntax_getNumArgs(v_stx_5829_);
                v___x_5934_ = lean_nat_dec_eq(v___x_5933_, v_snd_5932_);
                v___x_5935_ = 1;
                if v___x_5934_ == 0 {
                    crate::leanh::lean_dec(v___x_5933_);
                    crate::leanh::lean_inc(v_stx_5829_);
                    v___y_5859_ = v___y_5925_;
                    v___y_5860_ = v___y_5926_;
                    v___y_5861_ = v___x_5935_;
                    v___y_5862_ = v_fst_5931_;
                    v___y_5863_ = v___y_5927_;
                    v___y_5864_ = v___y_5929_;
                    v___y_5865_ = v___y_5928_;
                    v___y_5866_ = v___y_5930_;
                    v___y_5867_ = v_stx_5829_;
                    state = 4;
                    continue;
                } else {
                    v___x_5936_ = l_Lean_Syntax_getArgs(v_stx_5829_);
                    v___x_5937_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5938_ = lean_nat_sub(v___x_5933_, v___x_5937_);
                    crate::leanh::lean_dec(v___x_5933_);
                    v___x_5939_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5940_ =
                        l_Array_toSubarray___redArg(v___x_5936_, v___x_5939_, v___x_5938_);
                    v___x_5941_ = l_Subarray_copy___redArg(v___x_5940_);
                    crate::leanh::lean_inc(v_stx_5829_);
                    v___x_5942_ = l_Lean_Syntax_setArgs(v_stx_5829_, v___x_5941_);
                    v___y_5859_ = v___y_5925_;
                    v___y_5860_ = v___y_5926_;
                    v___y_5861_ = v___x_5935_;
                    v___y_5862_ = v_fst_5931_;
                    v___y_5863_ = v___y_5927_;
                    v___y_5864_ = v___y_5929_;
                    v___y_5865_ = v___y_5928_;
                    v___y_5866_ = v___y_5930_;
                    v___y_5867_ = v___x_5942_;
                    state = 4;
                    continue;
                }
            }
            12 => {
                v___x_5950_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_5951_ = l_Lean_Syntax_getArg(v_stx_5829_, v___x_5950_);
                v___x_5952_ = crate::leanh::lean_unsigned_to_nat(5);
                v___y_5925_ = v___y_5944_;
                v___y_5926_ = v___y_5945_;
                v___y_5927_ = v___y_5946_;
                v___y_5928_ = v___y_5948_;
                v___y_5929_ = v___y_5947_;
                v___y_5930_ = v___y_5949_;
                v_fst_5931_ = v___x_5951_;
                v_snd_5932_ = v___x_5952_;
                state = 11;
                continue;
            }
            13 => {
                if v___y_5960_ == 0 {
                    v___x_5961_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
                    crate::leanh::lean_inc(v_stx_5829_);
                    v___x_5962_ = l_Lean_Syntax_isOfKind(v_stx_5829_, v___x_5961_);
                    if v___x_5962_ == 0 {
                        v___x_5963_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5964_ = l_Lean_Syntax_getArg(v_stx_5829_, v___x_5963_);
                        v___x_5965_ = crate::leanh::lean_unsigned_to_nat(4);
                        v___y_5925_ = v___y_5954_;
                        v___y_5926_ = v___y_5955_;
                        v___y_5927_ = v___y_5956_;
                        v___y_5928_ = v___y_5958_;
                        v___y_5929_ = v___y_5957_;
                        v___y_5930_ = v___y_5959_;
                        v_fst_5931_ = v___x_5964_;
                        v_snd_5932_ = v___x_5965_;
                        state = 11;
                        continue;
                    } else {
                        v___y_5944_ = v___y_5954_;
                        v___y_5945_ = v___y_5955_;
                        v___y_5946_ = v___y_5956_;
                        v___y_5947_ = v___y_5957_;
                        v___y_5948_ = v___y_5958_;
                        v___y_5949_ = v___y_5959_;
                        state = 12;
                        continue;
                    }
                } else {
                    v___y_5944_ = v___y_5954_;
                    v___y_5945_ = v___y_5955_;
                    v___y_5946_ = v___y_5956_;
                    v___y_5947_ = v___y_5957_;
                    v___y_5948_ = v___y_5958_;
                    v___y_5949_ = v___y_5959_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v___x_5973_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
                crate::leanh::lean_inc(v_stx_5829_);
                v___x_5974_ = l_Lean_Syntax_isOfKind(v_stx_5829_, v___x_5973_);
                if v___x_5974_ == 0 {
                    v___x_5975_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
                    crate::leanh::lean_inc(v_stx_5829_);
                    v___x_5976_ = l_Lean_Syntax_isOfKind(v_stx_5829_, v___x_5975_);
                    v___y_5954_ = v___y_5972_;
                    v___y_5955_ = v___y_5969_;
                    v___y_5956_ = v___y_5968_;
                    v___y_5957_ = v___y_5970_;
                    v___y_5958_ = v___y_5967_;
                    v___y_5959_ = v___y_5971_;
                    v___y_5960_ = v___x_5976_;
                    state = 13;
                    continue;
                } else {
                    v___y_5954_ = v___y_5972_;
                    v___y_5955_ = v___y_5969_;
                    v___y_5956_ = v___y_5968_;
                    v___y_5957_ = v___y_5970_;
                    v___y_5958_ = v___y_5967_;
                    v___y_5959_ = v___y_5971_;
                    v___y_5960_ = v___x_5974_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_5986_ = lean_st_ref_get(v_a_5836_);
                v_env_5987_ = crate::leanh::lean_ctor_get(v___x_5986_, 0);
                crate::leanh::lean_inc_ref(v_env_5987_);
                crate::leanh::lean_dec(v___x_5986_);
                v___x_5988_ = 1;
                crate::leanh::lean_inc(v_snd_5982_);
                v___x_5989_ = l_Lean_Environment_contains(v_env_5987_, v_snd_5982_, v___x_5988_);
                if v___x_5989_ == 0 {
                    crate::leanh::lean_dec(v_expType_x3f_5830_);
                    crate::leanh::lean_dec(v_stx_5829_);
                    v___x_5990_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once
                        ),
                        _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11,
                    );
                    v___x_5991_ = l_Lean_MessageData_ofName(v_snd_5982_);
                    if v_isShared_5985_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5984_, 7);
                        crate::leanh::lean_ctor_set(v___x_5984_, 1, v___x_5991_);
                        crate::leanh::lean_ctor_set(v___x_5984_, 0, v___x_5990_);
                        v___x_5993_ = v___x_5984_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6012_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_5990_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___x_5991_);
                        v___x_5993_ = v_reuseFailAlloc_6012_;
                        state = 16;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5984_);
                    crate::leanh::lean_dec(v_snd_5982_);
                    crate::leanh::lean_dec(v_fst_5981_);
                    v___y_5967_ = v_a_5831_;
                    v___y_5968_ = v_a_5832_;
                    v___y_5969_ = v_a_5833_;
                    v___y_5970_ = v_a_5834_;
                    v___y_5971_ = v_a_5835_;
                    v___y_5972_ = v_a_5836_;
                    state = 14;
                    continue;
                }
            }
            16 => {
                v___x_5994_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once
                    ),
                    _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13,
                );
                v___x_5995_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5995_, 0, v___x_5993_);
                crate::leanh::lean_ctor_set(v___x_5995_, 1, v___x_5994_);
                v___x_5996_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once
                    ),
                    _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15,
                );
                v___x_5997_ = l_Lean_MessageData_ofName(v_fst_5981_);
                v___x_5998_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5998_, 0, v___x_5996_);
                crate::leanh::lean_ctor_set(v___x_5998_, 1, v___x_5997_);
                v___x_5999_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once
                    ),
                    _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17,
                );
                v___x_6000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6000_, 0, v___x_5998_);
                crate::leanh::lean_ctor_set(v___x_6000_, 1, v___x_5999_);
                v___x_6001_ = l_Lean_MessageData_hint_x27(v___x_6000_);
                v___x_6002_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6002_, 0, v___x_5995_);
                crate::leanh::lean_ctor_set(v___x_6002_, 1, v___x_6001_);
                v___x_6003_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_6002_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
                v_a_6004_ = crate::leanh::lean_ctor_get(v___x_6003_, 0);
                v_isSharedCheck_6011_ = (!crate::leanh::lean_is_exclusive(v___x_6003_)) as u8;
                if v_isSharedCheck_6011_ == 0 {
                    v___x_6006_ = v___x_6003_;
                    v_isShared_6007_ = v_isSharedCheck_6011_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6004_);
                    crate::leanh::lean_dec(v___x_6003_);
                    v___x_6006_ = crate::leanh::lean_box(0);
                    v_isShared_6007_ = v_isSharedCheck_6011_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_6007_ == 0 {
                    v___x_6009_ = v___x_6006_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
                    v___x_6009_ = v_reuseFailAlloc_6010_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6009_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed(
    mut v_stx_6014_: *mut crate::leanh::LeanObject,
    mut v_expType_x3f_6015_: *mut crate::leanh::LeanObject,
    mut v_a_6016_: *mut crate::leanh::LeanObject,
    mut v_a_6017_: *mut crate::leanh::LeanObject,
    mut v_a_6018_: *mut crate::leanh::LeanObject,
    mut v_a_6019_: *mut crate::leanh::LeanObject,
    mut v_a_6020_: *mut crate::leanh::LeanObject,
    mut v_a_6021_: *mut crate::leanh::LeanObject,
    mut v_a_6022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6023_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(
        v_stx_6014_,
        v_expType_x3f_6015_,
        v_a_6016_,
        v_a_6017_,
        v_a_6018_,
        v_a_6019_,
        v_a_6020_,
        v_a_6021_,
    );
    crate::leanh::lean_dec(v_a_6021_);
    crate::leanh::lean_dec_ref(v_a_6020_);
    crate::leanh::lean_dec(v_a_6019_);
    crate::leanh::lean_dec_ref(v_a_6018_);
    crate::leanh::lean_dec(v_a_6017_);
    crate::leanh::lean_dec_ref(v_a_6016_);
    return v_res_6023_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(
    mut v_00_u03b1_6024_: *mut crate::leanh::LeanObject,
    mut v_x_6025_: *mut crate::leanh::LeanObject,
    mut v___y_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6028_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_6025_, v___y_6027_);
    return v___x_6028_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(
    mut v_00_u03b1_6029_: *mut crate::leanh::LeanObject,
    mut v_x_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6033_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_6029_, v_x_6030_, v___y_6031_, v___y_6032_);
    crate::leanh::lean_dec_ref(v___y_6031_);
    crate::leanh::lean_dec_ref(v_x_6030_);
    return v_res_6033_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(
    mut v_00_u03b1_6034_: *mut crate::leanh::LeanObject,
    mut v_ref_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
    mut v___y_6037_: *mut crate::leanh::LeanObject,
    mut v___y_6038_: *mut crate::leanh::LeanObject,
    mut v___y_6039_: *mut crate::leanh::LeanObject,
    mut v___y_6040_: *mut crate::leanh::LeanObject,
    mut v___y_6041_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6043_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_6035_);
    return v___x_6043_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(
    mut v_00_u03b1_6044_: *mut crate::leanh::LeanObject,
    mut v_ref_6045_: *mut crate::leanh::LeanObject,
    mut v___y_6046_: *mut crate::leanh::LeanObject,
    mut v___y_6047_: *mut crate::leanh::LeanObject,
    mut v___y_6048_: *mut crate::leanh::LeanObject,
    mut v___y_6049_: *mut crate::leanh::LeanObject,
    mut v___y_6050_: *mut crate::leanh::LeanObject,
    mut v___y_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6053_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_6044_, v_ref_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_);
    crate::leanh::lean_dec(v___y_6051_);
    crate::leanh::lean_dec_ref(v___y_6050_);
    crate::leanh::lean_dec(v___y_6049_);
    crate::leanh::lean_dec_ref(v___y_6048_);
    crate::leanh::lean_dec(v___y_6047_);
    crate::leanh::lean_dec_ref(v___y_6046_);
    return v_res_6053_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(
    mut v_00_u03b1_6054_: *mut crate::leanh::LeanObject,
    mut v___y_6055_: *mut crate::leanh::LeanObject,
    mut v___y_6056_: *mut crate::leanh::LeanObject,
    mut v___y_6057_: *mut crate::leanh::LeanObject,
    mut v___y_6058_: *mut crate::leanh::LeanObject,
    mut v___y_6059_: *mut crate::leanh::LeanObject,
    mut v___y_6060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
    return v___x_6062_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(
    mut v_00_u03b1_6063_: *mut crate::leanh::LeanObject,
    mut v___y_6064_: *mut crate::leanh::LeanObject,
    mut v___y_6065_: *mut crate::leanh::LeanObject,
    mut v___y_6066_: *mut crate::leanh::LeanObject,
    mut v___y_6067_: *mut crate::leanh::LeanObject,
    mut v___y_6068_: *mut crate::leanh::LeanObject,
    mut v___y_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_6063_, v___y_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_);
    crate::leanh::lean_dec(v___y_6069_);
    crate::leanh::lean_dec_ref(v___y_6068_);
    crate::leanh::lean_dec(v___y_6067_);
    crate::leanh::lean_dec_ref(v___y_6066_);
    crate::leanh::lean_dec(v___y_6065_);
    crate::leanh::lean_dec_ref(v___y_6064_);
    return v_res_6071_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(
    mut v_00_u03b1_6072_: *mut crate::leanh::LeanObject,
    mut v_x_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6081_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
    return v___x_6081_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(
    mut v_00_u03b1_6082_: *mut crate::leanh::LeanObject,
    mut v_x_6083_: *mut crate::leanh::LeanObject,
    mut v___y_6084_: *mut crate::leanh::LeanObject,
    mut v___y_6085_: *mut crate::leanh::LeanObject,
    mut v___y_6086_: *mut crate::leanh::LeanObject,
    mut v___y_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6091_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(
            v_00_u03b1_6082_,
            v_x_6083_,
            v___y_6084_,
            v___y_6085_,
            v___y_6086_,
            v___y_6087_,
            v___y_6088_,
            v___y_6089_,
        );
    crate::leanh::lean_dec(v___y_6089_);
    crate::leanh::lean_dec_ref(v___y_6088_);
    crate::leanh::lean_dec(v___y_6087_);
    crate::leanh::lean_dec_ref(v___y_6086_);
    crate::leanh::lean_dec(v___y_6085_);
    crate::leanh::lean_dec_ref(v___y_6084_);
    return v_res_6091_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(
    mut v_t_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
    mut v___y_6094_: *mut crate::leanh::LeanObject,
    mut v___y_6095_: *mut crate::leanh::LeanObject,
    mut v___y_6096_: *mut crate::leanh::LeanObject,
    mut v___y_6097_: *mut crate::leanh::LeanObject,
    mut v___y_6098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6100_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_6092_, v___y_6098_);
    return v___x_6100_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(
    mut v_t_6101_: *mut crate::leanh::LeanObject,
    mut v___y_6102_: *mut crate::leanh::LeanObject,
    mut v___y_6103_: *mut crate::leanh::LeanObject,
    mut v___y_6104_: *mut crate::leanh::LeanObject,
    mut v___y_6105_: *mut crate::leanh::LeanObject,
    mut v___y_6106_: *mut crate::leanh::LeanObject,
    mut v___y_6107_: *mut crate::leanh::LeanObject,
    mut v___y_6108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6109_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
    crate::leanh::lean_dec(v___y_6107_);
    crate::leanh::lean_dec_ref(v___y_6106_);
    crate::leanh::lean_dec(v___y_6105_);
    crate::leanh::lean_dec_ref(v___y_6104_);
    crate::leanh::lean_dec(v___y_6103_);
    crate::leanh::lean_dec_ref(v___y_6102_);
    return v_res_6109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(
    mut v_00_u03b2_6110_: *mut crate::leanh::LeanObject,
    mut v_m_6111_: *mut crate::leanh::LeanObject,
    mut v_a_6112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_6111_, v_a_6112_);
    return v___x_6113_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(
    mut v_00_u03b2_6114_: *mut crate::leanh::LeanObject,
    mut v_m_6115_: *mut crate::leanh::LeanObject,
    mut v_a_6116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_6114_, v_m_6115_, v_a_6116_);
    crate::leanh::lean_dec(v_a_6116_);
    crate::leanh::lean_dec_ref(v_m_6115_);
    return v_res_6117_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(
    mut v_00_u03b1_6118_: *mut crate::leanh::LeanObject,
    mut v_msg_6119_: *mut crate::leanh::LeanObject,
    mut v___y_6120_: *mut crate::leanh::LeanObject,
    mut v___y_6121_: *mut crate::leanh::LeanObject,
    mut v___y_6122_: *mut crate::leanh::LeanObject,
    mut v___y_6123_: *mut crate::leanh::LeanObject,
    mut v___y_6124_: *mut crate::leanh::LeanObject,
    mut v___y_6125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6127_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
    return v___x_6127_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(
    mut v_00_u03b1_6128_: *mut crate::leanh::LeanObject,
    mut v_msg_6129_: *mut crate::leanh::LeanObject,
    mut v___y_6130_: *mut crate::leanh::LeanObject,
    mut v___y_6131_: *mut crate::leanh::LeanObject,
    mut v___y_6132_: *mut crate::leanh::LeanObject,
    mut v___y_6133_: *mut crate::leanh::LeanObject,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6137_ =
        l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(
            v_00_u03b1_6128_,
            v_msg_6129_,
            v___y_6130_,
            v___y_6131_,
            v___y_6132_,
            v___y_6133_,
            v___y_6134_,
            v___y_6135_,
        );
    crate::leanh::lean_dec(v___y_6135_);
    crate::leanh::lean_dec_ref(v___y_6134_);
    crate::leanh::lean_dec(v___y_6133_);
    crate::leanh::lean_dec_ref(v___y_6132_);
    crate::leanh::lean_dec(v___y_6131_);
    crate::leanh::lean_dec_ref(v___y_6130_);
    return v_res_6137_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(
    mut v_cls_6138_: *mut crate::leanh::LeanObject,
    mut v_msg_6139_: *mut crate::leanh::LeanObject,
    mut v___y_6140_: *mut crate::leanh::LeanObject,
    mut v___y_6141_: *mut crate::leanh::LeanObject,
    mut v___y_6142_: *mut crate::leanh::LeanObject,
    mut v___y_6143_: *mut crate::leanh::LeanObject,
    mut v___y_6144_: *mut crate::leanh::LeanObject,
    mut v___y_6145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6147_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_6138_, v_msg_6139_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_);
    return v___x_6147_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(
    mut v_cls_6148_: *mut crate::leanh::LeanObject,
    mut v_msg_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
    mut v___y_6151_: *mut crate::leanh::LeanObject,
    mut v___y_6152_: *mut crate::leanh::LeanObject,
    mut v___y_6153_: *mut crate::leanh::LeanObject,
    mut v___y_6154_: *mut crate::leanh::LeanObject,
    mut v___y_6155_: *mut crate::leanh::LeanObject,
    mut v___y_6156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6157_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_6148_, v_msg_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
    crate::leanh::lean_dec(v___y_6155_);
    crate::leanh::lean_dec_ref(v___y_6154_);
    crate::leanh::lean_dec(v___y_6153_);
    crate::leanh::lean_dec_ref(v___y_6152_);
    crate::leanh::lean_dec(v___y_6151_);
    crate::leanh::lean_dec_ref(v___y_6150_);
    return v_res_6157_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(
    mut v_as_6158_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6159_: *mut crate::leanh::LeanObject,
    mut v_b_6160_: *mut crate::leanh::LeanObject,
    mut v_a_6161_: *mut crate::leanh::LeanObject,
    mut v___y_6162_: *mut crate::leanh::LeanObject,
    mut v___y_6163_: *mut crate::leanh::LeanObject,
    mut v___y_6164_: *mut crate::leanh::LeanObject,
    mut v___y_6165_: *mut crate::leanh::LeanObject,
    mut v___y_6166_: *mut crate::leanh::LeanObject,
    mut v___y_6167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6169_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_6159_, v_b_6160_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
    return v___x_6169_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(
    mut v_as_6170_: *mut crate::leanh::LeanObject,
    mut v_as_x27_6171_: *mut crate::leanh::LeanObject,
    mut v_b_6172_: *mut crate::leanh::LeanObject,
    mut v_a_6173_: *mut crate::leanh::LeanObject,
    mut v___y_6174_: *mut crate::leanh::LeanObject,
    mut v___y_6175_: *mut crate::leanh::LeanObject,
    mut v___y_6176_: *mut crate::leanh::LeanObject,
    mut v___y_6177_: *mut crate::leanh::LeanObject,
    mut v___y_6178_: *mut crate::leanh::LeanObject,
    mut v___y_6179_: *mut crate::leanh::LeanObject,
    mut v___y_6180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6181_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_6170_, v_as_x27_6171_, v_b_6172_, v_a_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
    crate::leanh::lean_dec(v___y_6179_);
    crate::leanh::lean_dec_ref(v___y_6178_);
    crate::leanh::lean_dec(v___y_6177_);
    crate::leanh::lean_dec_ref(v___y_6176_);
    crate::leanh::lean_dec(v___y_6175_);
    crate::leanh::lean_dec_ref(v___y_6174_);
    crate::leanh::lean_dec(v_as_x27_6171_);
    crate::leanh::lean_dec(v_as_6170_);
    return v_res_6181_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(
    mut v_00_u03b1_6182_: *mut crate::leanh::LeanObject,
    mut v_ref_6183_: *mut crate::leanh::LeanObject,
    mut v_msg_6184_: *mut crate::leanh::LeanObject,
    mut v___y_6185_: *mut crate::leanh::LeanObject,
    mut v___y_6186_: *mut crate::leanh::LeanObject,
    mut v___y_6187_: *mut crate::leanh::LeanObject,
    mut v___y_6188_: *mut crate::leanh::LeanObject,
    mut v___y_6189_: *mut crate::leanh::LeanObject,
    mut v___y_6190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6192_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_6183_, v_msg_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
    return v___x_6192_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(
    mut v_00_u03b1_6193_: *mut crate::leanh::LeanObject,
    mut v_ref_6194_: *mut crate::leanh::LeanObject,
    mut v_msg_6195_: *mut crate::leanh::LeanObject,
    mut v___y_6196_: *mut crate::leanh::LeanObject,
    mut v___y_6197_: *mut crate::leanh::LeanObject,
    mut v___y_6198_: *mut crate::leanh::LeanObject,
    mut v___y_6199_: *mut crate::leanh::LeanObject,
    mut v___y_6200_: *mut crate::leanh::LeanObject,
    mut v___y_6201_: *mut crate::leanh::LeanObject,
    mut v___y_6202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6203_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_6193_, v_ref_6194_, v_msg_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
    crate::leanh::lean_dec(v___y_6201_);
    crate::leanh::lean_dec_ref(v___y_6200_);
    crate::leanh::lean_dec(v___y_6199_);
    crate::leanh::lean_dec_ref(v___y_6198_);
    crate::leanh::lean_dec(v___y_6197_);
    crate::leanh::lean_dec_ref(v___y_6196_);
    crate::leanh::lean_dec(v_ref_6194_);
    return v_res_6203_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(
    mut v_ref_6204_: *mut crate::leanh::LeanObject,
    mut v_msgData_6205_: *mut crate::leanh::LeanObject,
    mut v_severity_6206_: u8,
    mut v_isSilent_6207_: u8,
    mut v___y_6208_: *mut crate::leanh::LeanObject,
    mut v___y_6209_: *mut crate::leanh::LeanObject,
    mut v___y_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
    mut v___y_6212_: *mut crate::leanh::LeanObject,
    mut v___y_6213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6215_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_6204_, v_msgData_6205_, v_severity_6206_, v_isSilent_6207_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
    return v___x_6215_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(
    mut v_ref_6216_: *mut crate::leanh::LeanObject,
    mut v_msgData_6217_: *mut crate::leanh::LeanObject,
    mut v_severity_6218_: *mut crate::leanh::LeanObject,
    mut v_isSilent_6219_: *mut crate::leanh::LeanObject,
    mut v___y_6220_: *mut crate::leanh::LeanObject,
    mut v___y_6221_: *mut crate::leanh::LeanObject,
    mut v___y_6222_: *mut crate::leanh::LeanObject,
    mut v___y_6223_: *mut crate::leanh::LeanObject,
    mut v___y_6224_: *mut crate::leanh::LeanObject,
    mut v___y_6225_: *mut crate::leanh::LeanObject,
    mut v___y_6226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_6227_: u8 = 0;
    let mut v_isSilent_boxed_6228_: u8 = 0;
    let mut v_res_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_6227_ = (crate::leanh::lean_unbox(v_severity_6218_) as u8);
    v_isSilent_boxed_6228_ = (crate::leanh::lean_unbox(v_isSilent_6219_) as u8);
    v_res_6229_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_6216_, v_msgData_6217_, v_severity_boxed_6227_, v_isSilent_boxed_6228_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_);
    crate::leanh::lean_dec(v___y_6225_);
    crate::leanh::lean_dec_ref(v___y_6224_);
    crate::leanh::lean_dec(v___y_6223_);
    crate::leanh::lean_dec_ref(v___y_6222_);
    crate::leanh::lean_dec(v___y_6221_);
    crate::leanh::lean_dec_ref(v___y_6220_);
    crate::leanh::lean_dec(v_ref_6216_);
    return v_res_6229_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(
    mut v_00_u03b2_6230_: *mut crate::leanh::LeanObject,
    mut v_a_6231_: *mut crate::leanh::LeanObject,
    mut v_x_6232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_6231_, v_x_6232_);
    return v___x_6233_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(
    mut v_00_u03b2_6234_: *mut crate::leanh::LeanObject,
    mut v_a_6235_: *mut crate::leanh::LeanObject,
    mut v_x_6236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_6234_, v_a_6235_, v_x_6236_);
    crate::leanh::lean_dec(v_x_6236_);
    crate::leanh::lean_dec(v_a_6235_);
    return v_res_6237_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(
    mut v_msgData_6238_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
    mut v___y_6242_: *mut crate::leanh::LeanObject,
    mut v___y_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6247_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_6238_, v_macroStack_6239_, v___y_6244_);
    return v___x_6247_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(
    mut v_msgData_6248_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6249_: *mut crate::leanh::LeanObject,
    mut v___y_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6257_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_6248_, v_macroStack_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
    crate::leanh::lean_dec(v___y_6255_);
    crate::leanh::lean_dec_ref(v___y_6254_);
    crate::leanh::lean_dec(v___y_6253_);
    crate::leanh::lean_dec_ref(v___y_6252_);
    crate::leanh::lean_dec(v___y_6251_);
    crate::leanh::lean_dec_ref(v___y_6250_);
    return v_res_6257_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(
    mut v_00_u03b2_6258_: *mut crate::leanh::LeanObject,
    mut v_x_6259_: *mut crate::leanh::LeanObject,
    mut v_x_6260_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6261_: u8 = 0;
    v___x_6261_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_6259_, v_x_6260_);
    return v___x_6261_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(
    mut v_00_u03b2_6262_: *mut crate::leanh::LeanObject,
    mut v_x_6263_: *mut crate::leanh::LeanObject,
    mut v_x_6264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6265_: u8 = 0;
    let mut v_r_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6265_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_6262_, v_x_6263_, v_x_6264_);
    crate::leanh::lean_dec_ref(v_x_6264_);
    crate::leanh::lean_dec_ref(v_x_6263_);
    v_r_6266_ = crate::leanh::lean_box((v_res_6265_) as usize);
    return v_r_6266_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(
    mut v_00_u03b2_6267_: *mut crate::leanh::LeanObject,
    mut v_x_6268_: *mut crate::leanh::LeanObject,
    mut v_x_6269_: usize,
    mut v_x_6270_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6271_: u8 = 0;
    v___x_6271_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_6268_, v_x_6269_, v_x_6270_);
    return v___x_6271_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(
    mut v_00_u03b2_6272_: *mut crate::leanh::LeanObject,
    mut v_x_6273_: *mut crate::leanh::LeanObject,
    mut v_x_6274_: *mut crate::leanh::LeanObject,
    mut v_x_6275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_22597__boxed_6276_: usize = 0;
    let mut v_res_6277_: u8 = 0;
    let mut v_r_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_22597__boxed_6276_ = crate::leanh::lean_unbox_usize(v_x_6274_);
    crate::leanh::lean_dec(v_x_6274_);
    v_res_6277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_6272_, v_x_6273_, v_x_22597__boxed_6276_, v_x_6275_);
    crate::leanh::lean_dec_ref(v_x_6275_);
    crate::leanh::lean_dec_ref(v_x_6273_);
    v_r_6278_ = crate::leanh::lean_box((v_res_6277_) as usize);
    return v_r_6278_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(
    mut v_00_u03b2_6279_: *mut crate::leanh::LeanObject,
    mut v_keys_6280_: *mut crate::leanh::LeanObject,
    mut v_vals_6281_: *mut crate::leanh::LeanObject,
    mut v_heq_6282_: *mut crate::leanh::LeanObject,
    mut v_i_6283_: *mut crate::leanh::LeanObject,
    mut v_k_6284_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_6285_: u8 = 0;
    v___x_6285_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_6280_, v_i_6283_, v_k_6284_);
    return v___x_6285_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(
    mut v_00_u03b2_6286_: *mut crate::leanh::LeanObject,
    mut v_keys_6287_: *mut crate::leanh::LeanObject,
    mut v_vals_6288_: *mut crate::leanh::LeanObject,
    mut v_heq_6289_: *mut crate::leanh::LeanObject,
    mut v_i_6290_: *mut crate::leanh::LeanObject,
    mut v_k_6291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6292_: u8 = 0;
    let mut v_r_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6292_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_6286_, v_keys_6287_, v_vals_6288_, v_heq_6289_, v_i_6290_, v_k_6291_);
    crate::leanh::lean_dec_ref(v_k_6291_);
    crate::leanh::lean_dec_ref(v_vals_6288_);
    crate::leanh::lean_dec_ref(v_keys_6287_);
    v_r_6293_ = crate::leanh::lean_box((v_res_6292_) as usize);
    return v_r_6293_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6302_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6303_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
    v___x_6304_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6305_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6306_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6302_,
        v___x_6303_,
        v___x_6304_,
        v___x_6305_,
    );
    return v___x_6306_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___boxed(
    mut v_a_6307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6308_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
    return v_res_6308_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6310_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6311_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
    v___x_6312_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6313_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6314_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6310_,
        v___x_6311_,
        v___x_6312_,
        v___x_6313_,
    );
    return v___x_6314_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3___boxed(
    mut v_a_6315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6316_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
    return v_res_6316_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6318_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6319_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
    v___x_6320_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6321_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6322_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6318_,
        v___x_6319_,
        v___x_6320_,
        v___x_6321_,
    );
    return v___x_6322_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5___boxed(
    mut v_a_6323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6324_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
    return v_res_6324_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6326_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6327_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
    v___x_6328_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6329_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6330_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6326_,
        v___x_6327_,
        v___x_6328_,
        v___x_6329_,
    );
    return v___x_6330_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7___boxed(
    mut v_a_6331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6332_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
    return v_res_6332_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6334_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6335_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
    v___x_6336_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6337_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6338_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6334_,
        v___x_6335_,
        v___x_6336_,
        v___x_6337_,
    );
    return v___x_6338_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9___boxed(
    mut v_a_6339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6340_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
    return v_res_6340_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6342_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6343_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
    v___x_6344_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6345_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6346_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6342_,
        v___x_6343_,
        v___x_6344_,
        v___x_6345_,
    );
    return v___x_6346_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11___boxed(
    mut v_a_6347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6348_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
    return v_res_6348_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6349_ = crate::leanh::lean_box(0);
    v___x_6350_ = l_Lean_Elab_abortTermExceptionId;
    v___x_6351_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6351_, 0, v___x_6350_);
    crate::leanh::lean_ctor_set(v___x_6351_, 1, v___x_6349_);
    return v___x_6351_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0);
    v___x_6354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6354_, 0, v___x_6353_);
    return v___x_6354_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___boxed(
    mut v___y_6355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6356_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
    return v_res_6356_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(
    mut v_00_u03b1_6357_: *mut crate::leanh::LeanObject,
    mut v___y_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
    mut v___y_6360_: *mut crate::leanh::LeanObject,
    mut v___y_6361_: *mut crate::leanh::LeanObject,
    mut v___y_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6365_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
    return v___x_6365_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___boxed(
    mut v_00_u03b1_6366_: *mut crate::leanh::LeanObject,
    mut v___y_6367_: *mut crate::leanh::LeanObject,
    mut v___y_6368_: *mut crate::leanh::LeanObject,
    mut v___y_6369_: *mut crate::leanh::LeanObject,
    mut v___y_6370_: *mut crate::leanh::LeanObject,
    mut v___y_6371_: *mut crate::leanh::LeanObject,
    mut v___y_6372_: *mut crate::leanh::LeanObject,
    mut v___y_6373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6374_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(v_00_u03b1_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_);
    crate::leanh::lean_dec(v___y_6372_);
    crate::leanh::lean_dec_ref(v___y_6371_);
    crate::leanh::lean_dec(v___y_6370_);
    crate::leanh::lean_dec_ref(v___y_6369_);
    crate::leanh::lean_dec(v___y_6368_);
    crate::leanh::lean_dec_ref(v___y_6367_);
    return v_res_6374_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(
    mut v_t_6375_: *mut crate::leanh::LeanObject,
    mut v_tp_6376_: *mut crate::leanh::LeanObject,
    mut v_a_6377_: *mut crate::leanh::LeanObject,
    mut v_a_6378_: *mut crate::leanh::LeanObject,
    mut v_a_6379_: *mut crate::leanh::LeanObject,
    mut v_a_6380_: *mut crate::leanh::LeanObject,
    mut v_a_6381_: *mut crate::leanh::LeanObject,
    mut v_a_6382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: u8 = 0;
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: u8 = 0;
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: u8 = 0;
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6401_: u8 = 0;
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut v_a_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_tp_6376_);
                v___x_6384_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6384_, 0, v_tp_6376_);
                v___x_6385_ = 1;
                v___x_6386_ = crate::leanh::lean_box(0);
                v___x_6387_ = l_Lean_Elab_Term_elabTermEnsuringType(
                    v_t_6375_,
                    v___x_6384_,
                    v___x_6385_,
                    v___x_6385_,
                    v___x_6386_,
                    v_a_6377_,
                    v_a_6378_,
                    v_a_6379_,
                    v_a_6380_,
                    v_a_6381_,
                    v_a_6382_,
                );
                if crate::leanh::lean_obj_tag(v___x_6387_) == 0 {
                    v_a_6388_ = crate::leanh::lean_ctor_get(v___x_6387_, 0);
                    crate::leanh::lean_inc(v_a_6388_);
                    crate::leanh::lean_dec_ref_known(v___x_6387_, 1);
                    v___x_6396_ = l_Lean_Expr_hasSyntheticSorry(v_a_6388_);
                    if v___x_6396_ == 0 {
                        v___y_6390_ = v_a_6379_;
                        v___y_6391_ = v_a_6380_;
                        v___y_6392_ = v_a_6381_;
                        v___y_6393_ = v_a_6382_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6397_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
                        if crate::leanh::lean_obj_tag(v___x_6397_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6397_, 1);
                            v___y_6390_ = v_a_6379_;
                            v___y_6391_ = v_a_6380_;
                            v___y_6392_ = v_a_6381_;
                            v___y_6393_ = v_a_6382_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6388_);
                            crate::leanh::lean_dec_ref(v_tp_6376_);
                            v_a_6398_ = crate::leanh::lean_ctor_get(v___x_6397_, 0);
                            v_isSharedCheck_6405_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6397_)) as u8;
                            if v_isSharedCheck_6405_ == 0 {
                                v___x_6400_ = v___x_6397_;
                                v_isShared_6401_ = v_isSharedCheck_6405_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6398_);
                                crate::leanh::lean_dec(v___x_6397_);
                                v___x_6400_ = crate::leanh::lean_box(0);
                                v_isShared_6401_ = v_isSharedCheck_6405_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_tp_6376_);
                    v_a_6406_ = crate::leanh::lean_ctor_get(v___x_6387_, 0);
                    v_isSharedCheck_6413_ = (!crate::leanh::lean_is_exclusive(v___x_6387_)) as u8;
                    if v_isSharedCheck_6413_ == 0 {
                        v___x_6408_ = v___x_6387_;
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6406_);
                        crate::leanh::lean_dec(v___x_6387_);
                        v___x_6408_ = crate::leanh::lean_box(0);
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6394_ = 1;
                v___x_6395_ = l_Lean_Meta_evalExpr___redArg(
                    v_tp_6376_,
                    v_a_6388_,
                    v___x_6394_,
                    v___x_6385_,
                    v___y_6390_,
                    v___y_6391_,
                    v___y_6392_,
                    v___y_6393_,
                );
                return v___x_6395_;
            }
            2 => {
                if v_isShared_6401_ == 0 {
                    v___x_6403_ = v___x_6400_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_a_6398_);
                    v___x_6403_ = v_reuseFailAlloc_6404_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6403_;
            }
            4 => {
                if v_isShared_6409_ == 0 {
                    v___x_6411_ = v___x_6408_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6412_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6412_, 0, v_a_6406_);
                    v___x_6411_ = v_reuseFailAlloc_6412_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1___boxed(
    mut v_t_6414_: *mut crate::leanh::LeanObject,
    mut v_tp_6415_: *mut crate::leanh::LeanObject,
    mut v_a_6416_: *mut crate::leanh::LeanObject,
    mut v_a_6417_: *mut crate::leanh::LeanObject,
    mut v_a_6418_: *mut crate::leanh::LeanObject,
    mut v_a_6419_: *mut crate::leanh::LeanObject,
    mut v_a_6420_: *mut crate::leanh::LeanObject,
    mut v_a_6421_: *mut crate::leanh::LeanObject,
    mut v_a_6422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6423_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_6414_, v_tp_6415_, v_a_6416_, v_a_6417_, v_a_6418_, v_a_6419_, v_a_6420_, v_a_6421_);
    crate::leanh::lean_dec(v_a_6421_);
    crate::leanh::lean_dec_ref(v_a_6420_);
    crate::leanh::lean_dec(v_a_6419_);
    crate::leanh::lean_dec_ref(v_a_6418_);
    crate::leanh::lean_dec(v_a_6417_);
    crate::leanh::lean_dec_ref(v_a_6416_);
    return v_res_6423_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6425_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
    v___x_6426_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6426_, 0, v___x_6425_);
    return v___x_6426_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(
    mut v___y_6427_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6428_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
    return v_res_6428_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(
    mut v_00_u03b1_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
    mut v___y_6431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6433_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
    return v___x_6433_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(
    mut v_00_u03b1_6434_: *mut crate::leanh::LeanObject,
    mut v___y_6435_: *mut crate::leanh::LeanObject,
    mut v___y_6436_: *mut crate::leanh::LeanObject,
    mut v___y_6437_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_6434_, v___y_6435_, v___y_6436_);
    crate::leanh::lean_dec(v___y_6436_);
    crate::leanh::lean_dec_ref(v___y_6435_);
    return v_res_6438_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(
    mut v___y_6439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6441_ = lean_st_ref_get(v___y_6439_);
    v_env_6442_ = crate::leanh::lean_ctor_get(v___x_6441_, 0);
    crate::leanh::lean_inc_ref(v_env_6442_);
    crate::leanh::lean_dec(v___x_6441_);
    v___x_6443_ = l_Lean_Environment_header(v_env_6442_);
    crate::leanh::lean_dec_ref(v_env_6442_);
    v_mainModule_6444_ = crate::leanh::lean_ctor_get(v___x_6443_, 0);
    crate::leanh::lean_inc(v_mainModule_6444_);
    crate::leanh::lean_dec_ref(v___x_6443_);
    v___x_6445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6445_, 0, v_mainModule_6444_);
    return v___x_6445_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6448_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_6446_);
    crate::leanh::lean_dec(v___y_6446_);
    return v_res_6448_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(
    mut v___y_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6452_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_6450_);
    return v___x_6452_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
    mut v___y_6455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6456_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v___y_6453_, v___y_6454_);
    crate::leanh::lean_dec(v___y_6454_);
    crate::leanh::lean_dec_ref(v___y_6453_);
    return v_res_6456_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(
    mut v_t_6457_: *mut crate::leanh::LeanObject,
    mut v___x_6458_: *mut crate::leanh::LeanObject,
    mut v_x_6459_: *mut crate::leanh::LeanObject,
    mut v___y_6460_: *mut crate::leanh::LeanObject,
    mut v___y_6461_: *mut crate::leanh::LeanObject,
    mut v___y_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6467_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_6457_, v___x_6458_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
    return v___x_6467_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(
    mut v_t_6468_: *mut crate::leanh::LeanObject,
    mut v___x_6469_: *mut crate::leanh::LeanObject,
    mut v_x_6470_: *mut crate::leanh::LeanObject,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
    mut v___y_6472_: *mut crate::leanh::LeanObject,
    mut v___y_6473_: *mut crate::leanh::LeanObject,
    mut v___y_6474_: *mut crate::leanh::LeanObject,
    mut v___y_6475_: *mut crate::leanh::LeanObject,
    mut v___y_6476_: *mut crate::leanh::LeanObject,
    mut v___y_6477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6478_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(
        v_t_6468_,
        v___x_6469_,
        v_x_6470_,
        v___y_6471_,
        v___y_6472_,
        v___y_6473_,
        v___y_6474_,
        v___y_6475_,
        v___y_6476_,
    );
    crate::leanh::lean_dec(v___y_6476_);
    crate::leanh::lean_dec_ref(v___y_6475_);
    crate::leanh::lean_dec(v___y_6474_);
    crate::leanh::lean_dec_ref(v___y_6473_);
    crate::leanh::lean_dec(v___y_6472_);
    crate::leanh::lean_dec_ref(v___y_6471_);
    crate::leanh::lean_dec_ref(v_x_6470_);
    return v_res_6478_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(
    mut v_msgData_6479_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6480_: *mut crate::leanh::LeanObject,
    mut v___y_6481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: u8 = 0;
    let mut v___x_6490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6496_: u8 = 0;
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_6504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6508_: u8 = 0;
    let mut v_unused_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6483_ = lean_st_ref_get(v___y_6481_);
                v_scopes_6484_ = crate::leanh::lean_ctor_get(v___x_6483_, 2);
                crate::leanh::lean_inc(v_scopes_6484_);
                crate::leanh::lean_dec(v___x_6483_);
                v___x_6485_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_6486_ = l_List_head_x21___redArg(v___x_6485_, v_scopes_6484_);
                crate::leanh::lean_dec(v_scopes_6484_);
                v_opts_6487_ = crate::leanh::lean_ctor_get(v___x_6486_, 1);
                crate::leanh::lean_inc_ref(v_opts_6487_);
                crate::leanh::lean_dec(v___x_6486_);
                v___x_6488_ = l_Lean_Elab_pp_macroStack;
                v___x_6489_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_6487_, v___x_6488_);
                crate::leanh::lean_dec_ref(v_opts_6487_);
                if v___x_6489_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_6480_);
                    v___x_6490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6490_, 0, v_msgData_6479_);
                    return v___x_6490_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_6480_) == 0 {
                        v___x_6491_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6491_, 0, v_msgData_6479_);
                        return v___x_6491_;
                    } else {
                        v_head_6492_ = crate::leanh::lean_ctor_get(v_macroStack_6480_, 0);
                        crate::leanh::lean_inc(v_head_6492_);
                        v_after_6493_ = crate::leanh::lean_ctor_get(v_head_6492_, 1);
                        v_isSharedCheck_6508_ =
                            (!crate::leanh::lean_is_exclusive(v_head_6492_)) as u8;
                        if v_isSharedCheck_6508_ == 0 {
                            v_unused_6509_ = crate::leanh::lean_ctor_get(v_head_6492_, 0);
                            crate::leanh::lean_dec(v_unused_6509_);
                            v___x_6495_ = v_head_6492_;
                            v_isShared_6496_ = v_isSharedCheck_6508_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_6493_);
                            crate::leanh::lean_dec(v_head_6492_);
                            v___x_6495_ = crate::leanh::lean_box(0);
                            v_isShared_6496_ = v_isSharedCheck_6508_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6497_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
                if v_isShared_6496_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6495_, 7);
                    crate::leanh::lean_ctor_set(v___x_6495_, 1, v___x_6497_);
                    crate::leanh::lean_ctor_set(v___x_6495_, 0, v_msgData_6479_);
                    v___x_6499_ = v___x_6495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6507_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_msgData_6479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6507_, 1, v___x_6497_);
                    v___x_6499_ = v_reuseFailAlloc_6507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6500_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
                v___x_6501_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6501_, 0, v___x_6499_);
                crate::leanh::lean_ctor_set(v___x_6501_, 1, v___x_6500_);
                v___x_6502_ = l_Lean_MessageData_ofSyntax(v_after_6493_);
                v___x_6503_ = l_Lean_indentD(v___x_6502_);
                v_msgData_6504_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_6504_, 0, v___x_6501_);
                crate::leanh::lean_ctor_set(v_msgData_6504_, 1, v___x_6503_);
                v___x_6505_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_6504_, v_macroStack_6480_);
                v___x_6506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6506_, 0, v___x_6505_);
                return v___x_6506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg___boxed(
    mut v_msgData_6510_: *mut crate::leanh::LeanObject,
    mut v_macroStack_6511_: *mut crate::leanh::LeanObject,
    mut v___y_6512_: *mut crate::leanh::LeanObject,
    mut v___y_6513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6514_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_6510_, v_macroStack_6511_, v___y_6512_);
    crate::leanh::lean_dec(v___y_6512_);
    return v_res_6514_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6515_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6516_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0);
    v___x_6517_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6517_, 0, v___x_6516_);
    return v___x_6517_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
    v___x_6519_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6520_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6520_, 0, v___x_6519_);
    crate::leanh::lean_ctor_set(v___x_6520_, 1, v___x_6519_);
    crate::leanh::lean_ctor_set(v___x_6520_, 2, v___x_6519_);
    crate::leanh::lean_ctor_set(v___x_6520_, 3, v___x_6519_);
    crate::leanh::lean_ctor_set(v___x_6520_, 4, v___x_6518_);
    crate::leanh::lean_ctor_set(v___x_6520_, 5, v___x_6518_);
    crate::leanh::lean_ctor_set(v___x_6520_, 6, v___x_6518_);
    crate::leanh::lean_ctor_set(v___x_6520_, 7, v___x_6518_);
    crate::leanh::lean_ctor_set(v___x_6520_, 8, v___x_6518_);
    crate::leanh::lean_ctor_set(v___x_6520_, 9, v___x_6518_);
    return v___x_6520_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6521_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6522_ = lean_mk_empty_array_with_capacity(v___x_6521_);
    v___x_6523_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6523_, 0, v___x_6522_);
    return v___x_6523_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6524_: usize = 0;
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6524_ = 5usize;
    v___x_6525_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6526_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6527_ = lean_mk_empty_array_with_capacity(v___x_6526_);
    v___x_6528_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3);
    v___x_6529_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6529_, 0, v___x_6528_);
    crate::leanh::lean_ctor_set(v___x_6529_, 1, v___x_6527_);
    crate::leanh::lean_ctor_set(v___x_6529_, 2, v___x_6525_);
    crate::leanh::lean_ctor_set(v___x_6529_, 3, v___x_6525_);
    crate::leanh::lean_ctor_set_usize(v___x_6529_, 4, v___x_6524_);
    return v___x_6529_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6530_ = crate::leanh::lean_box(1);
    v___x_6531_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4);
    v___x_6532_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
    v___x_6533_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6533_, 0, v___x_6532_);
    crate::leanh::lean_ctor_set(v___x_6533_, 1, v___x_6531_);
    crate::leanh::lean_ctor_set(v___x_6533_, 2, v___x_6530_);
    return v___x_6533_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(
    mut v_msgData_6534_: *mut crate::leanh::LeanObject,
    mut v___y_6535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6537_ = lean_st_ref_get(v___y_6535_);
    v_env_6538_ = crate::leanh::lean_ctor_get(v___x_6537_, 0);
    crate::leanh::lean_inc_ref(v_env_6538_);
    crate::leanh::lean_dec(v___x_6537_);
    v___x_6539_ = lean_st_ref_get(v___y_6535_);
    v_scopes_6540_ = crate::leanh::lean_ctor_get(v___x_6539_, 2);
    crate::leanh::lean_inc(v_scopes_6540_);
    crate::leanh::lean_dec(v___x_6539_);
    v___x_6541_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_6542_ = l_List_head_x21___redArg(v___x_6541_, v_scopes_6540_);
    crate::leanh::lean_dec(v_scopes_6540_);
    v_opts_6543_ = crate::leanh::lean_ctor_get(v___x_6542_, 1);
    crate::leanh::lean_inc_ref(v_opts_6543_);
    crate::leanh::lean_dec(v___x_6542_);
    v___x_6544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2);
    v___x_6545_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5);
    v___x_6546_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6546_, 0, v_env_6538_);
    crate::leanh::lean_ctor_set(v___x_6546_, 1, v___x_6544_);
    crate::leanh::lean_ctor_set(v___x_6546_, 2, v___x_6545_);
    crate::leanh::lean_ctor_set(v___x_6546_, 3, v_opts_6543_);
    v___x_6547_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6547_, 0, v___x_6546_);
    crate::leanh::lean_ctor_set(v___x_6547_, 1, v_msgData_6534_);
    v___x_6548_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6548_, 0, v___x_6547_);
    return v___x_6548_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___boxed(
    mut v_msgData_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6552_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_6549_, v___y_6550_);
    crate::leanh::lean_dec(v___y_6550_);
    return v_res_6552_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(
    mut v_msg_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6567_: u8 = 0;
    let mut v___x_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6572_: u8 = 0;
    let mut v_a_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6576_: u8 = 0;
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6557_ = l_Lean_Elab_Command_getRef___redArg(v___y_6554_);
                if crate::leanh::lean_obj_tag(v___x_6557_) == 0 {
                    v_a_6558_ = crate::leanh::lean_ctor_get(v___x_6557_, 0);
                    crate::leanh::lean_inc(v_a_6558_);
                    crate::leanh::lean_dec_ref_known(v___x_6557_, 1);
                    v_macroStack_6559_ = crate::leanh::lean_ctor_get(v___y_6554_, 4);
                    v___x_6560_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_6553_, v___y_6555_);
                    v_a_6561_ = crate::leanh::lean_ctor_get(v___x_6560_, 0);
                    crate::leanh::lean_inc(v_a_6561_);
                    crate::leanh::lean_dec_ref(v___x_6560_);
                    v___x_6562_ = l_Lean_Elab_getBetterRef(v_a_6558_, v_macroStack_6559_);
                    crate::leanh::lean_dec(v_a_6558_);
                    crate::leanh::lean_inc(v_macroStack_6559_);
                    v___x_6563_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_a_6561_, v_macroStack_6559_, v___y_6555_);
                    v_a_6564_ = crate::leanh::lean_ctor_get(v___x_6563_, 0);
                    v_isSharedCheck_6572_ = (!crate::leanh::lean_is_exclusive(v___x_6563_)) as u8;
                    if v_isSharedCheck_6572_ == 0 {
                        v___x_6566_ = v___x_6563_;
                        v_isShared_6567_ = v_isSharedCheck_6572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6564_);
                        crate::leanh::lean_dec(v___x_6563_);
                        v___x_6566_ = crate::leanh::lean_box(0);
                        v_isShared_6567_ = v_isSharedCheck_6572_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_6553_);
                    v_a_6573_ = crate::leanh::lean_ctor_get(v___x_6557_, 0);
                    v_isSharedCheck_6580_ = (!crate::leanh::lean_is_exclusive(v___x_6557_)) as u8;
                    if v_isSharedCheck_6580_ == 0 {
                        v___x_6575_ = v___x_6557_;
                        v_isShared_6576_ = v_isSharedCheck_6580_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6573_);
                        crate::leanh::lean_dec(v___x_6557_);
                        v___x_6575_ = crate::leanh::lean_box(0);
                        v_isShared_6576_ = v_isSharedCheck_6580_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6568_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6568_, 0, v___x_6562_);
                crate::leanh::lean_ctor_set(v___x_6568_, 1, v_a_6564_);
                if v_isShared_6567_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6566_, 1);
                    crate::leanh::lean_ctor_set(v___x_6566_, 0, v___x_6568_);
                    v___x_6570_ = v___x_6566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6571_, 0, v___x_6568_);
                    v___x_6570_ = v_reuseFailAlloc_6571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6570_;
            }
            3 => {
                if v_isShared_6576_ == 0 {
                    v___x_6578_ = v___x_6575_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_a_6573_);
                    v___x_6578_ = v_reuseFailAlloc_6579_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6578_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg___boxed(
    mut v_msg_6581_: *mut crate::leanh::LeanObject,
    mut v___y_6582_: *mut crate::leanh::LeanObject,
    mut v___y_6583_: *mut crate::leanh::LeanObject,
    mut v___y_6584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6585_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_6581_, v___y_6582_, v___y_6583_);
    crate::leanh::lean_dec(v___y_6583_);
    crate::leanh::lean_dec_ref(v___y_6582_);
    return v_res_6585_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(
    mut v_ref_6586_: *mut crate::leanh::LeanObject,
    mut v_msg_6587_: *mut crate::leanh::LeanObject,
    mut v___y_6588_: *mut crate::leanh::LeanObject,
    mut v___y_6589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6602_: u8 = 0;
    let mut v_ref_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6609_: u8 = 0;
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6591_ = l_Lean_Elab_Command_getRef___redArg(v___y_6588_);
                if crate::leanh::lean_obj_tag(v___x_6591_) == 0 {
                    v_a_6592_ = crate::leanh::lean_ctor_get(v___x_6591_, 0);
                    crate::leanh::lean_inc(v_a_6592_);
                    crate::leanh::lean_dec_ref_known(v___x_6591_, 1);
                    v_fileName_6593_ = crate::leanh::lean_ctor_get(v___y_6588_, 0);
                    v_fileMap_6594_ = crate::leanh::lean_ctor_get(v___y_6588_, 1);
                    v_currRecDepth_6595_ = crate::leanh::lean_ctor_get(v___y_6588_, 2);
                    v_cmdPos_6596_ = crate::leanh::lean_ctor_get(v___y_6588_, 3);
                    v_macroStack_6597_ = crate::leanh::lean_ctor_get(v___y_6588_, 4);
                    v_quotContext_x3f_6598_ = crate::leanh::lean_ctor_get(v___y_6588_, 5);
                    v_currMacroScope_6599_ = crate::leanh::lean_ctor_get(v___y_6588_, 6);
                    v_snap_x3f_6600_ = crate::leanh::lean_ctor_get(v___y_6588_, 8);
                    v_cancelTk_x3f_6601_ = crate::leanh::lean_ctor_get(v___y_6588_, 9);
                    v_suppressElabErrors_6602_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_6588_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_6603_ = l_Lean_replaceRef(v_ref_6586_, v_a_6592_);
                    crate::leanh::lean_dec(v_a_6592_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_6601_);
                    crate::leanh::lean_inc(v_snap_x3f_6600_);
                    crate::leanh::lean_inc(v_currMacroScope_6599_);
                    crate::leanh::lean_inc(v_quotContext_x3f_6598_);
                    crate::leanh::lean_inc(v_macroStack_6597_);
                    crate::leanh::lean_inc(v_cmdPos_6596_);
                    crate::leanh::lean_inc(v_currRecDepth_6595_);
                    crate::leanh::lean_inc_ref(v_fileMap_6594_);
                    crate::leanh::lean_inc_ref(v_fileName_6593_);
                    v___x_6604_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_6604_, 0, v_fileName_6593_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 1, v_fileMap_6594_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 2, v_currRecDepth_6595_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 3, v_cmdPos_6596_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 4, v_macroStack_6597_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 5, v_quotContext_x3f_6598_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 6, v_currMacroScope_6599_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 7, v_ref_6603_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 8, v_snap_x3f_6600_);
                    crate::leanh::lean_ctor_set(v___x_6604_, 9, v_cancelTk_x3f_6601_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6604_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_6602_,
                    );
                    v___x_6605_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_6587_, v___x_6604_, v___y_6589_);
                    crate::leanh::lean_dec_ref_known(v___x_6604_, 10);
                    return v___x_6605_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_6587_);
                    v_a_6606_ = crate::leanh::lean_ctor_get(v___x_6591_, 0);
                    v_isSharedCheck_6613_ = (!crate::leanh::lean_is_exclusive(v___x_6591_)) as u8;
                    if v_isSharedCheck_6613_ == 0 {
                        v___x_6608_ = v___x_6591_;
                        v_isShared_6609_ = v_isSharedCheck_6613_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6606_);
                        crate::leanh::lean_dec(v___x_6591_);
                        v___x_6608_ = crate::leanh::lean_box(0);
                        v_isShared_6609_ = v_isSharedCheck_6613_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6609_ == 0 {
                    v___x_6611_ = v___x_6608_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_a_6606_);
                    v___x_6611_ = v_reuseFailAlloc_6612_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6611_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg___boxed(
    mut v_ref_6614_: *mut crate::leanh::LeanObject,
    mut v_msg_6615_: *mut crate::leanh::LeanObject,
    mut v___y_6616_: *mut crate::leanh::LeanObject,
    mut v___y_6617_: *mut crate::leanh::LeanObject,
    mut v___y_6618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6619_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_6614_, v_msg_6615_, v___y_6616_, v___y_6617_);
    crate::leanh::lean_dec(v___y_6617_);
    crate::leanh::lean_dec_ref(v___y_6616_);
    crate::leanh::lean_dec(v_ref_6614_);
    return v_res_6619_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(
    mut v_cls_6620_: *mut crate::leanh::LeanObject,
    mut v_msg_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6646_: u8 = 0;
    let mut v_tid_6647_: u64 = 0;
    let mut v_traces_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: f64 = 0.0;
    let mut v___x_6654_: u8 = 0;
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6672_: u8 = 0;
    let mut v_isSharedCheck_6673_: u8 = 0;
    let mut v_isSharedCheck_6674_: u8 = 0;
    let mut v_a_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6678_: u8 = 0;
    let mut v___x_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6625_ = l_Lean_Elab_Command_getRef___redArg(v___y_6622_);
                if crate::leanh::lean_obj_tag(v___x_6625_) == 0 {
                    v_a_6626_ = crate::leanh::lean_ctor_get(v___x_6625_, 0);
                    crate::leanh::lean_inc(v_a_6626_);
                    crate::leanh::lean_dec_ref_known(v___x_6625_, 1);
                    v___x_6627_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_6621_, v___y_6623_);
                    v_a_6628_ = crate::leanh::lean_ctor_get(v___x_6627_, 0);
                    v_isSharedCheck_6674_ = (!crate::leanh::lean_is_exclusive(v___x_6627_)) as u8;
                    if v_isSharedCheck_6674_ == 0 {
                        v___x_6630_ = v___x_6627_;
                        v_isShared_6631_ = v_isSharedCheck_6674_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6628_);
                        crate::leanh::lean_dec(v___x_6627_);
                        v___x_6630_ = crate::leanh::lean_box(0);
                        v_isShared_6631_ = v_isSharedCheck_6674_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_6621_);
                    crate::leanh::lean_dec(v_cls_6620_);
                    v_a_6675_ = crate::leanh::lean_ctor_get(v___x_6625_, 0);
                    v_isSharedCheck_6682_ = (!crate::leanh::lean_is_exclusive(v___x_6625_)) as u8;
                    if v_isSharedCheck_6682_ == 0 {
                        v___x_6677_ = v___x_6625_;
                        v_isShared_6678_ = v_isSharedCheck_6682_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6675_);
                        crate::leanh::lean_dec(v___x_6625_);
                        v___x_6677_ = crate::leanh::lean_box(0);
                        v_isShared_6678_ = v_isSharedCheck_6682_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6632_ = lean_st_ref_take(v___y_6623_);
                v_traceState_6633_ = crate::leanh::lean_ctor_get(v___x_6632_, 9);
                v_env_6634_ = crate::leanh::lean_ctor_get(v___x_6632_, 0);
                v_messages_6635_ = crate::leanh::lean_ctor_get(v___x_6632_, 1);
                v_scopes_6636_ = crate::leanh::lean_ctor_get(v___x_6632_, 2);
                v_usedQuotCtxts_6637_ = crate::leanh::lean_ctor_get(v___x_6632_, 3);
                v_nextMacroScope_6638_ = crate::leanh::lean_ctor_get(v___x_6632_, 4);
                v_maxRecDepth_6639_ = crate::leanh::lean_ctor_get(v___x_6632_, 5);
                v_ngen_6640_ = crate::leanh::lean_ctor_get(v___x_6632_, 6);
                v_auxDeclNGen_6641_ = crate::leanh::lean_ctor_get(v___x_6632_, 7);
                v_infoState_6642_ = crate::leanh::lean_ctor_get(v___x_6632_, 8);
                v_snapshotTasks_6643_ = crate::leanh::lean_ctor_get(v___x_6632_, 10);
                v_isSharedCheck_6673_ = (!crate::leanh::lean_is_exclusive(v___x_6632_)) as u8;
                if v_isSharedCheck_6673_ == 0 {
                    v___x_6645_ = v___x_6632_;
                    v_isShared_6646_ = v_isSharedCheck_6673_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6643_);
                    crate::leanh::lean_inc(v_traceState_6633_);
                    crate::leanh::lean_inc(v_infoState_6642_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6641_);
                    crate::leanh::lean_inc(v_ngen_6640_);
                    crate::leanh::lean_inc(v_maxRecDepth_6639_);
                    crate::leanh::lean_inc(v_nextMacroScope_6638_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_6637_);
                    crate::leanh::lean_inc(v_scopes_6636_);
                    crate::leanh::lean_inc(v_messages_6635_);
                    crate::leanh::lean_inc(v_env_6634_);
                    crate::leanh::lean_dec(v___x_6632_);
                    v___x_6645_ = crate::leanh::lean_box(0);
                    v_isShared_6646_ = v_isSharedCheck_6673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6647_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6633_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6648_ = crate::leanh::lean_ctor_get(v_traceState_6633_, 0);
                v_isSharedCheck_6672_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6633_)) as u8;
                if v_isSharedCheck_6672_ == 0 {
                    v___x_6650_ = v_traceState_6633_;
                    v_isShared_6651_ = v_isSharedCheck_6672_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_6648_);
                    crate::leanh::lean_dec(v_traceState_6633_);
                    v___x_6650_ = crate::leanh::lean_box(0);
                    v_isShared_6651_ = v_isSharedCheck_6672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6652_ = crate::leanh::lean_box(0);
                v___x_6653_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
                v___x_6654_ = 0;
                v___x_6655_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                v___x_6656_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_6656_, 0, v_cls_6620_);
                crate::leanh::lean_ctor_set(v___x_6656_, 1, v___x_6652_);
                crate::leanh::lean_ctor_set(v___x_6656_, 2, v___x_6655_);
                crate::leanh::lean_ctor_set_float(
                    v___x_6656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6653_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_6656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6653_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6656_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6654_,
                );
                v___x_6657_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2;
                v___x_6658_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6658_, 0, v___x_6656_);
                crate::leanh::lean_ctor_set(v___x_6658_, 1, v_a_6628_);
                crate::leanh::lean_ctor_set(v___x_6658_, 2, v___x_6657_);
                v___x_6659_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6659_, 0, v_a_6626_);
                crate::leanh::lean_ctor_set(v___x_6659_, 1, v___x_6658_);
                v___x_6660_ = l_Lean_PersistentArray_push___redArg(v_traces_6648_, v___x_6659_);
                if v_isShared_6651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6650_, 0, v___x_6660_);
                    v___x_6662_ = v___x_6650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6671_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6671_, 0, v___x_6660_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6671_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6647_,
                    );
                    v___x_6662_ = v_reuseFailAlloc_6671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6646_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6645_, 9, v___x_6662_);
                    v___x_6664_ = v___x_6645_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_env_6634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 1, v_messages_6635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 2, v_scopes_6636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 3, v_usedQuotCtxts_6637_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 4, v_nextMacroScope_6638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 5, v_maxRecDepth_6639_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 6, v_ngen_6640_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 7, v_auxDeclNGen_6641_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 8, v_infoState_6642_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 9, v___x_6662_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6670_, 10, v_snapshotTasks_6643_);
                    v___x_6664_ = v_reuseFailAlloc_6670_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6665_ = lean_st_ref_set(v___y_6623_, v___x_6664_);
                v___x_6666_ = crate::leanh::lean_box(0);
                if v_isShared_6631_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6630_, 0, v___x_6666_);
                    v___x_6668_ = v___x_6630_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6669_, 0, v___x_6666_);
                    v___x_6668_ = v_reuseFailAlloc_6669_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6668_;
            }
            7 => {
                if v_isShared_6678_ == 0 {
                    v___x_6680_ = v___x_6677_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6681_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6681_, 0, v_a_6675_);
                    v___x_6680_ = v_reuseFailAlloc_6681_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3___boxed(
    mut v_cls_6683_: *mut crate::leanh::LeanObject,
    mut v_msg_6684_: *mut crate::leanh::LeanObject,
    mut v___y_6685_: *mut crate::leanh::LeanObject,
    mut v___y_6686_: *mut crate::leanh::LeanObject,
    mut v___y_6687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6688_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_6683_, v_msg_6684_, v___y_6685_, v___y_6686_);
    crate::leanh::lean_dec(v___y_6686_);
    crate::leanh::lean_dec_ref(v___y_6685_);
    return v_res_6688_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(
    mut v_mod_6689_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6690_: u8,
    mut v_hint_6691_: *mut crate::leanh::LeanObject,
    mut v___y_6692_: *mut crate::leanh::LeanObject,
    mut v___y_6693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6697_: u8 = 0;
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6722_: u8 = 0;
    let mut v_asyncMode_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6731_: u8 = 0;
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: u8 = 0;
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6741_: u8 = 0;
    let mut v_cls_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: u8 = 0;
    let mut v___x_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: u8 = 0;
    let mut v___x_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6695_ = lean_st_ref_get(v___y_6693_);
                v_env_6696_ = crate::leanh::lean_ctor_get(v___x_6695_, 0);
                crate::leanh::lean_inc_ref(v_env_6696_);
                crate::leanh::lean_dec(v___x_6695_);
                v_isExporting_6697_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_6696_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_6696_);
                v___x_6698_ = lean_st_ref_get(v___y_6693_);
                v_env_6699_ = crate::leanh::lean_ctor_get(v___x_6698_, 0);
                crate::leanh::lean_inc_ref(v_env_6699_);
                crate::leanh::lean_dec(v___x_6698_);
                v___x_6700_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
                crate::leanh::lean_inc(v_mod_6689_);
                v_entry_6701_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_6701_, 0, v_mod_6689_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_6701_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_6697_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_6701_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_6690_,
                );
                v___x_6702_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_6703_ = crate::leanh::lean_box(1);
                v___x_6704_ = crate::leanh::lean_box(0);
                v___x_6732_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_6700_,
                    v___x_6702_,
                    v_env_6699_,
                    v___x_6703_,
                    v___x_6704_,
                );
                v___x_6733_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_6732_, v_entry_6701_);
                crate::leanh::lean_dec(v___x_6732_);
                if v___x_6733_ == 0 {
                    v___x_6734_ = l_Lean_inheritedTraceOptions;
                    v___x_6735_ = lean_st_ref_get(v___x_6734_);
                    v___x_6736_ = lean_st_ref_get(v___y_6693_);
                    v_scopes_6737_ = crate::leanh::lean_ctor_get(v___x_6736_, 2);
                    crate::leanh::lean_inc(v_scopes_6737_);
                    crate::leanh::lean_dec(v___x_6736_);
                    v___x_6738_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_6739_ = l_List_head_x21___redArg(v___x_6738_, v_scopes_6737_);
                    crate::leanh::lean_dec(v_scopes_6737_);
                    v_opts_6740_ = crate::leanh::lean_ctor_get(v___x_6739_, 1);
                    crate::leanh::lean_inc_ref(v_opts_6740_);
                    crate::leanh::lean_dec(v___x_6739_);
                    v_hasTrace_6741_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_6740_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6741_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_6740_);
                        crate::leanh::lean_dec(v___x_6735_);
                        crate::leanh::lean_dec(v_hint_6691_);
                        crate::leanh::lean_dec(v_mod_6689_);
                        v___y_6706_ = v___y_6693_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_6742_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
                        v___x_6762_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
                        v___x_6763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_6735_,
                            v_opts_6740_,
                            v___x_6762_,
                        );
                        crate::leanh::lean_dec_ref(v_opts_6740_);
                        crate::leanh::lean_dec(v___x_6735_);
                        if v___x_6763_ == 0 {
                            crate::leanh::lean_dec(v_hint_6691_);
                            crate::leanh::lean_dec(v_mod_6689_);
                            v___y_6706_ = v___y_6693_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6764_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
                            if v_isExporting_6697_ == 0 {
                                v___x_6773_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21;
                                v___y_6766_ = v___x_6773_;
                                state = 6;
                                continue;
                            } else {
                                v___x_6774_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22;
                                v___y_6766_ = v___x_6774_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_6701_, 1);
                    crate::leanh::lean_dec(v_hint_6691_);
                    crate::leanh::lean_dec(v_mod_6689_);
                    v___x_6775_ = crate::leanh::lean_box(0);
                    v___x_6776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6776_, 0, v___x_6775_);
                    return v___x_6776_;
                }
            }
            1 => {
                v___x_6707_ = lean_st_ref_take(v___y_6706_);
                v_toEnvExtension_6708_ = crate::leanh::lean_ctor_get(v___x_6702_, 0);
                v_env_6709_ = crate::leanh::lean_ctor_get(v___x_6707_, 0);
                v_messages_6710_ = crate::leanh::lean_ctor_get(v___x_6707_, 1);
                v_scopes_6711_ = crate::leanh::lean_ctor_get(v___x_6707_, 2);
                v_usedQuotCtxts_6712_ = crate::leanh::lean_ctor_get(v___x_6707_, 3);
                v_nextMacroScope_6713_ = crate::leanh::lean_ctor_get(v___x_6707_, 4);
                v_maxRecDepth_6714_ = crate::leanh::lean_ctor_get(v___x_6707_, 5);
                v_ngen_6715_ = crate::leanh::lean_ctor_get(v___x_6707_, 6);
                v_auxDeclNGen_6716_ = crate::leanh::lean_ctor_get(v___x_6707_, 7);
                v_infoState_6717_ = crate::leanh::lean_ctor_get(v___x_6707_, 8);
                v_traceState_6718_ = crate::leanh::lean_ctor_get(v___x_6707_, 9);
                v_snapshotTasks_6719_ = crate::leanh::lean_ctor_get(v___x_6707_, 10);
                v_isSharedCheck_6731_ = (!crate::leanh::lean_is_exclusive(v___x_6707_)) as u8;
                if v_isSharedCheck_6731_ == 0 {
                    v___x_6721_ = v___x_6707_;
                    v_isShared_6722_ = v_isSharedCheck_6731_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6719_);
                    crate::leanh::lean_inc(v_traceState_6718_);
                    crate::leanh::lean_inc(v_infoState_6717_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6716_);
                    crate::leanh::lean_inc(v_ngen_6715_);
                    crate::leanh::lean_inc(v_maxRecDepth_6714_);
                    crate::leanh::lean_inc(v_nextMacroScope_6713_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_6712_);
                    crate::leanh::lean_inc(v_scopes_6711_);
                    crate::leanh::lean_inc(v_messages_6710_);
                    crate::leanh::lean_inc(v_env_6709_);
                    crate::leanh::lean_dec(v___x_6707_);
                    v___x_6721_ = crate::leanh::lean_box(0);
                    v_isShared_6722_ = v_isSharedCheck_6731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_6723_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6708_, 2);
                v___x_6724_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6702_,
                    v_env_6709_,
                    v_entry_6701_,
                    v_asyncMode_6723_,
                    v___x_6704_,
                );
                if v_isShared_6722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6721_, 0, v___x_6724_);
                    v___x_6726_ = v___x_6721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6730_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 0, v___x_6724_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 1, v_messages_6710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 2, v_scopes_6711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 3, v_usedQuotCtxts_6712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 4, v_nextMacroScope_6713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 5, v_maxRecDepth_6714_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 6, v_ngen_6715_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 7, v_auxDeclNGen_6716_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 8, v_infoState_6717_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 9, v_traceState_6718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6730_, 10, v_snapshotTasks_6719_);
                    v___x_6726_ = v_reuseFailAlloc_6730_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6727_ = lean_st_ref_set(v___y_6706_, v___x_6726_);
                v___x_6728_ = crate::leanh::lean_box(0);
                v___x_6729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6729_, 0, v___x_6728_);
                return v___x_6729_;
            }
            4 => {
                v___x_6746_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6746_, 0, v___y_6744_);
                crate::leanh::lean_ctor_set(v___x_6746_, 1, v___y_6745_);
                v___x_6747_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_6742_, v___x_6746_, v___y_6692_, v___y_6693_);
                if crate::leanh::lean_obj_tag(v___x_6747_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6747_, 1);
                    v___y_6706_ = v___y_6693_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_6701_, 1);
                    return v___x_6747_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_6750_);
                v___x_6751_ = l_Lean_stringToMessageData(v___y_6750_);
                v___x_6752_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6752_, 0, v___y_6749_);
                crate::leanh::lean_ctor_set(v___x_6752_, 1, v___x_6751_);
                v___x_6753_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
                v___x_6754_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6754_, 0, v___x_6752_);
                crate::leanh::lean_ctor_set(v___x_6754_, 1, v___x_6753_);
                v___x_6755_ = l_Lean_MessageData_ofName(v_mod_6689_);
                v___x_6756_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6756_, 0, v___x_6754_);
                crate::leanh::lean_ctor_set(v___x_6756_, 1, v___x_6755_);
                v___x_6757_ = l_Lean_Name_isAnonymous(v_hint_6691_);
                if v___x_6757_ == 0 {
                    v___x_6758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
                    v___x_6759_ = l_Lean_MessageData_ofName(v_hint_6691_);
                    v___x_6760_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6760_, 0, v___x_6758_);
                    crate::leanh::lean_ctor_set(v___x_6760_, 1, v___x_6759_);
                    v___y_6744_ = v___x_6756_;
                    v___y_6745_ = v___x_6760_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_6691_);
                    v___x_6761_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
                    v___y_6744_ = v___x_6756_;
                    v___y_6745_ = v___x_6761_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_6766_);
                v___x_6767_ = l_Lean_stringToMessageData(v___y_6766_);
                v___x_6768_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6768_, 0, v___x_6764_);
                crate::leanh::lean_ctor_set(v___x_6768_, 1, v___x_6767_);
                v___x_6769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
                v___x_6770_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6770_, 0, v___x_6768_);
                crate::leanh::lean_ctor_set(v___x_6770_, 1, v___x_6769_);
                if v_isMeta_6690_ == 0 {
                    v___x_6771_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19;
                    v___y_6749_ = v___x_6770_;
                    v___y_6750_ = v___x_6771_;
                    state = 5;
                    continue;
                } else {
                    v___x_6772_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20;
                    v___y_6749_ = v___x_6770_;
                    v___y_6750_ = v___x_6772_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1___boxed(
    mut v_mod_6777_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6778_: *mut crate::leanh::LeanObject,
    mut v_hint_6779_: *mut crate::leanh::LeanObject,
    mut v___y_6780_: *mut crate::leanh::LeanObject,
    mut v___y_6781_: *mut crate::leanh::LeanObject,
    mut v___y_6782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6783_: u8 = 0;
    let mut v_res_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6783_ = (crate::leanh::lean_unbox(v_isMeta_6778_) as u8);
    v_res_6784_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_6777_, v_isMeta_boxed_6783_, v_hint_6779_, v___y_6780_, v___y_6781_);
    crate::leanh::lean_dec(v___y_6781_);
    crate::leanh::lean_dec_ref(v___y_6780_);
    return v_res_6784_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(
    mut v___x_6785_: *mut crate::leanh::LeanObject,
    mut v_declName_6786_: *mut crate::leanh::LeanObject,
    mut v_as_6787_: *mut crate::leanh::LeanObject,
    mut v_sz_6788_: usize,
    mut v_i_6789_: usize,
    mut v_b_6790_: *mut crate::leanh::LeanObject,
    mut v___y_6791_: *mut crate::leanh::LeanObject,
    mut v___y_6792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6794_: u8 = 0;
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: u8 = 0;
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: usize = 0;
    let mut v___x_6807_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6794_ = lean_usize_dec_lt(v_i_6789_, v_sz_6788_);
                if v___x_6794_ == 0 {
                    crate::leanh::lean_dec(v_declName_6786_);
                    v___x_6795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6795_, 0, v_b_6790_);
                    return v___x_6795_;
                } else {
                    v___x_6796_ = l_Lean_Environment_header(v___x_6785_);
                    v_modules_6797_ = crate::leanh::lean_ctor_get(v___x_6796_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6797_);
                    crate::leanh::lean_dec_ref(v___x_6796_);
                    v___x_6798_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_6799_ = lean_array_uget_borrowed(v_as_6787_, v_i_6789_);
                    v___x_6800_ = lean_array_get(v___x_6798_, v_modules_6797_, v_a_6799_);
                    crate::leanh::lean_dec_ref(v_modules_6797_);
                    v_toImport_6801_ = crate::leanh::lean_ctor_get(v___x_6800_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_6801_);
                    crate::leanh::lean_dec(v___x_6800_);
                    v_module_6802_ = crate::leanh::lean_ctor_get(v_toImport_6801_, 0);
                    crate::leanh::lean_inc(v_module_6802_);
                    crate::leanh::lean_dec_ref(v_toImport_6801_);
                    v___x_6803_ = 0;
                    crate::leanh::lean_inc(v_declName_6786_);
                    v___x_6804_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_6802_, v___x_6803_, v_declName_6786_, v___y_6791_, v___y_6792_);
                    if crate::leanh::lean_obj_tag(v___x_6804_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6804_, 1);
                        v___x_6805_ = crate::leanh::lean_box(0);
                        v___x_6806_ = 1usize;
                        v___x_6807_ = lean_usize_add(v_i_6789_, v___x_6806_);
                        v_i_6789_ = v___x_6807_;
                        v_b_6790_ = v___x_6805_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_6786_);
                        return v___x_6804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(
    mut v___x_6809_: *mut crate::leanh::LeanObject,
    mut v_declName_6810_: *mut crate::leanh::LeanObject,
    mut v_as_6811_: *mut crate::leanh::LeanObject,
    mut v_sz_6812_: *mut crate::leanh::LeanObject,
    mut v_i_6813_: *mut crate::leanh::LeanObject,
    mut v_b_6814_: *mut crate::leanh::LeanObject,
    mut v___y_6815_: *mut crate::leanh::LeanObject,
    mut v___y_6816_: *mut crate::leanh::LeanObject,
    mut v___y_6817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6818_: usize = 0;
    let mut v_i_boxed_6819_: usize = 0;
    let mut v_res_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6818_ = crate::leanh::lean_unbox_usize(v_sz_6812_);
    crate::leanh::lean_dec(v_sz_6812_);
    v_i_boxed_6819_ = crate::leanh::lean_unbox_usize(v_i_6813_);
    crate::leanh::lean_dec(v_i_6813_);
    v_res_6820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_6809_, v_declName_6810_, v_as_6811_, v_sz_boxed_6818_, v_i_boxed_6819_, v_b_6814_, v___y_6815_, v___y_6816_);
    crate::leanh::lean_dec(v___y_6816_);
    crate::leanh::lean_dec_ref(v___y_6815_);
    crate::leanh::lean_dec_ref(v_as_6811_);
    crate::leanh::lean_dec_ref(v___x_6809_);
    return v_res_6820_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(
    mut v_declName_6821_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6822_: u8,
    mut v___y_6823_: *mut crate::leanh::LeanObject,
    mut v___y_6824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6834_: usize = 0;
    let mut v___x_6835_: usize = 0;
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6839_: u8 = 0;
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6843_: u8 = 0;
    let mut v_unused_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u8 = 0;
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6856_: u8 = 0;
    let mut v_toImport_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: u8 = 0;
    let mut v___x_6868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6826_ = lean_st_ref_get(v___y_6824_);
                v_env_6830_ = crate::leanh::lean_ctor_get(v___x_6826_, 0);
                crate::leanh::lean_inc_ref(v_env_6830_);
                crate::leanh::lean_dec(v___x_6826_);
                v___x_6845_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6830_, v_declName_6821_);
                if crate::leanh::lean_obj_tag(v___x_6845_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_6830_);
                    crate::leanh::lean_dec(v_declName_6821_);
                    state = 1;
                    continue;
                } else {
                    v_val_6846_ = crate::leanh::lean_ctor_get(v___x_6845_, 0);
                    crate::leanh::lean_inc(v_val_6846_);
                    crate::leanh::lean_dec_ref_known(v___x_6845_, 1);
                    v___x_6847_ = l_Lean_Environment_header(v_env_6830_);
                    v_modules_6848_ = crate::leanh::lean_ctor_get(v___x_6847_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6848_);
                    crate::leanh::lean_dec_ref(v___x_6847_);
                    v___x_6849_ = lean_array_get_size(v_modules_6848_);
                    v___x_6850_ = lean_nat_dec_lt(v_val_6846_, v___x_6849_);
                    if v___x_6850_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_6848_);
                        crate::leanh::lean_dec(v_val_6846_);
                        crate::leanh::lean_dec_ref(v_env_6830_);
                        crate::leanh::lean_dec(v_declName_6821_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6851_ = lean_st_ref_get(v___y_6824_);
                        v_env_6852_ = crate::leanh::lean_ctor_get(v___x_6851_, 0);
                        crate::leanh::lean_inc_ref(v_env_6852_);
                        crate::leanh::lean_dec(v___x_6851_);
                        v___x_6853_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
                        v___x_6854_ = lean_array_fget(v_modules_6848_, v_val_6846_);
                        crate::leanh::lean_dec(v_val_6846_);
                        crate::leanh::lean_dec_ref(v_modules_6848_);
                        if v_isMeta_6822_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_6852_);
                            v___y_6856_ = v_isMeta_6822_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_6821_);
                            v___x_6867_ = l_Lean_isMarkedMeta(v_env_6852_, v_declName_6821_);
                            if v___x_6867_ == 0 {
                                v___y_6856_ = v_isMeta_6822_;
                                state = 5;
                                continue;
                            } else {
                                v___x_6868_ = 0;
                                v___y_6856_ = v___x_6868_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6828_ = crate::leanh::lean_box(0);
                v___x_6829_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6829_, 0, v___x_6828_);
                return v___x_6829_;
            }
            2 => {
                v___x_6833_ = crate::leanh::lean_box(0);
                v_sz_6834_ = lean_array_size(v___y_6832_);
                v___x_6835_ = 0usize;
                v___x_6836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_6830_, v_declName_6821_, v___y_6832_, v_sz_6834_, v___x_6835_, v___x_6833_, v___y_6823_, v___y_6824_);
                crate::leanh::lean_dec_ref(v___y_6832_);
                crate::leanh::lean_dec_ref(v_env_6830_);
                if crate::leanh::lean_obj_tag(v___x_6836_) == 0 {
                    v_isSharedCheck_6843_ = (!crate::leanh::lean_is_exclusive(v___x_6836_)) as u8;
                    if v_isSharedCheck_6843_ == 0 {
                        v_unused_6844_ = crate::leanh::lean_ctor_get(v___x_6836_, 0);
                        crate::leanh::lean_dec(v_unused_6844_);
                        v___x_6838_ = v___x_6836_;
                        v_isShared_6839_ = v_isSharedCheck_6843_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6836_);
                        v___x_6838_ = crate::leanh::lean_box(0);
                        v_isShared_6839_ = v_isSharedCheck_6843_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_6836_;
                }
            }
            3 => {
                if v_isShared_6839_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6838_, 0, v___x_6833_);
                    v___x_6841_ = v___x_6838_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6842_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6842_, 0, v___x_6833_);
                    v___x_6841_ = v_reuseFailAlloc_6842_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6841_;
            }
            5 => {
                v_toImport_6857_ = crate::leanh::lean_ctor_get(v___x_6854_, 0);
                crate::leanh::lean_inc_ref(v_toImport_6857_);
                crate::leanh::lean_dec(v___x_6854_);
                v_module_6858_ = crate::leanh::lean_ctor_get(v_toImport_6857_, 0);
                crate::leanh::lean_inc(v_module_6858_);
                crate::leanh::lean_dec_ref(v_toImport_6857_);
                crate::leanh::lean_inc(v_declName_6821_);
                v___x_6859_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_6858_, v___y_6856_, v_declName_6821_, v___y_6823_, v___y_6824_);
                if crate::leanh::lean_obj_tag(v___x_6859_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6859_, 1);
                    v___x_6860_ = l_Lean_indirectModUseExt;
                    v___x_6861_ = crate::leanh::lean_box(1);
                    v___x_6862_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_6830_);
                    v___x_6863_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_6853_,
                        v___x_6860_,
                        v_env_6830_,
                        v___x_6861_,
                        v___x_6862_,
                    );
                    v___x_6864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_6863_, v_declName_6821_);
                    crate::leanh::lean_dec(v___x_6863_);
                    if crate::leanh::lean_obj_tag(v___x_6864_) == 0 {
                        v___x_6865_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3;
                        v___y_6832_ = v___x_6865_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6866_ = crate::leanh::lean_ctor_get(v___x_6864_, 0);
                        crate::leanh::lean_inc(v_val_6866_);
                        crate::leanh::lean_dec_ref_known(v___x_6864_, 1);
                        v___y_6832_ = v_val_6866_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_6830_);
                    crate::leanh::lean_dec(v_declName_6821_);
                    return v___x_6859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(
    mut v_declName_6869_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6870_: *mut crate::leanh::LeanObject,
    mut v___y_6871_: *mut crate::leanh::LeanObject,
    mut v___y_6872_: *mut crate::leanh::LeanObject,
    mut v___y_6873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6874_: u8 = 0;
    let mut v_res_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6874_ = (crate::leanh::lean_unbox(v_isMeta_6870_) as u8);
    v_res_6875_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_6869_, v_isMeta_boxed_6874_, v___y_6871_, v___y_6872_);
    crate::leanh::lean_dec(v___y_6872_);
    crate::leanh::lean_dec_ref(v___y_6871_);
    return v_res_6875_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6884_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
    v___x_6885_ = l_Lean_stringToMessageData(v___x_6884_);
    return v___x_6885_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6886_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
    v___x_6887_ = l_Lean_stringToMessageData(v___x_6886_);
    return v___x_6887_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6889_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
    v___x_6890_ = l_Lean_stringToMessageData(v___x_6889_);
    return v___x_6890_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6892_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
    v___x_6893_ = l_Lean_stringToMessageData(v___x_6892_);
    return v___x_6893_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6895_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
    v___x_6896_ = l_Lean_stringToMessageData(v___x_6895_);
    return v___x_6896_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6897_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once
        ),
        _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11,
    );
    v___x_6898_ = l_Lean_MessageData_note(v___x_6897_);
    return v___x_6898_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6900_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13;
    v___x_6901_ = l_Lean_stringToMessageData(v___x_6900_);
    return v___x_6901_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6907_ = crate::leanh::lean_box(0);
    v___x_6908_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
    v___x_6909_ = l_Lean_mkConst(v___x_6908_, v___x_6907_);
    return v___x_6909_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6911_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18;
    v___x_6912_ = l_Lean_stringToMessageData(v___x_6911_);
    return v___x_6912_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6914_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20;
    v___x_6915_ = l_Lean_stringToMessageData(v___x_6914_);
    return v___x_6915_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(
    mut v_x_6916_: *mut crate::leanh::LeanObject,
    mut v_a_6917_: *mut crate::leanh::LeanObject,
    mut v_a_6918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v___x_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6947_: u8 = 0;
    let mut v___x_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6967_: u8 = 0;
    let mut v_isSharedCheck_6968_: u8 = 0;
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: u8 = 0;
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6981_: u8 = 0;
    let mut v___y_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: u8 = 0;
    let mut v___x_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: u8 = 0;
    let mut v___x_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: u8 = 0;
    let mut v___y_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: u8 = 0;
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: u8 = 0;
    let mut v___x_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7060_: u8 = 0;
    let mut v_env_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmd_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_t_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: u8 = 0;
    let mut v___x_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7085_: u8 = 0;
    let mut v___x_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7089_: u8 = 0;
    let mut v_ref_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: u8 = 0;
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7099_: u8 = 0;
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6969_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
                crate::leanh::lean_inc(v_x_6916_);
                v___x_6970_ = l_Lean_Syntax_isOfKind(v_x_6916_, v___x_6969_);
                if v___x_6970_ == 0 {
                    crate::leanh::lean_dec(v_x_6916_);
                    v___x_6971_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
                    return v___x_6971_;
                } else {
                    v___x_6972_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6973_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_6972_);
                    v___x_6974_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6975_ = l_Lean_Syntax_matchesNull(v___x_6973_, v___x_6974_);
                    if v___x_6975_ == 0 {
                        crate::leanh::lean_dec(v_x_6916_);
                        v___x_6976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
                        return v___x_6976_;
                    } else {
                        v___x_6977_ = crate::leanh::lean_unsigned_to_nat(2);
                        v_id_6978_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_6977_);
                        v___x_7018_ =
                            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
                        crate::leanh::lean_inc(v_id_6978_);
                        v___x_7019_ = l_Lean_Syntax_isOfKind(v_id_6978_, v___x_7018_);
                        if v___x_7019_ == 0 {
                            crate::leanh::lean_dec(v_id_6978_);
                            crate::leanh::lean_dec(v_x_6916_);
                            v___x_7047_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
                            return v___x_7047_;
                        } else {
                            v___x_7048_ = l_Lean_Elab_Command_getRef___redArg(v_a_6917_);
                            if crate::leanh::lean_obj_tag(v___x_7048_) == 0 {
                                v_a_7049_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                                crate::leanh::lean_inc(v_a_7049_);
                                crate::leanh::lean_dec_ref_known(v___x_7048_, 1);
                                v___x_7050_ = lean_st_ref_get(v_a_6918_);
                                v_fileName_7051_ = crate::leanh::lean_ctor_get(v_a_6917_, 0);
                                v_fileMap_7052_ = crate::leanh::lean_ctor_get(v_a_6917_, 1);
                                v_currRecDepth_7053_ = crate::leanh::lean_ctor_get(v_a_6917_, 2);
                                v_cmdPos_7054_ = crate::leanh::lean_ctor_get(v_a_6917_, 3);
                                v_macroStack_7055_ = crate::leanh::lean_ctor_get(v_a_6917_, 4);
                                v_quotContext_x3f_7056_ = crate::leanh::lean_ctor_get(v_a_6917_, 5);
                                v_currMacroScope_7057_ = crate::leanh::lean_ctor_get(v_a_6917_, 6);
                                v_snap_x3f_7058_ = crate::leanh::lean_ctor_get(v_a_6917_, 8);
                                v_cancelTk_x3f_7059_ = crate::leanh::lean_ctor_get(v_a_6917_, 9);
                                v_suppressElabErrors_7060_ = crate::leanh::lean_ctor_get_uint8(
                                    v_a_6917_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10)
                                        as u32,
                                );
                                v_env_7061_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                                crate::leanh::lean_inc_ref(v_env_7061_);
                                crate::leanh::lean_dec(v___x_7050_);
                                v_cmd_7062_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_6974_);
                                v___x_7063_ = crate::leanh::lean_unsigned_to_nat(3);
                                v_t_7064_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_7063_);
                                crate::leanh::lean_dec(v_x_6916_);
                                v_ref_7090_ = l_Lean_replaceRef(v_cmd_7062_, v_a_7049_);
                                crate::leanh::lean_dec(v_a_7049_);
                                crate::leanh::lean_dec(v_cmd_7062_);
                                crate::leanh::lean_inc(v_cancelTk_x3f_7059_);
                                crate::leanh::lean_inc(v_snap_x3f_7058_);
                                crate::leanh::lean_inc(v_currMacroScope_7057_);
                                crate::leanh::lean_inc(v_quotContext_x3f_7056_);
                                crate::leanh::lean_inc(v_macroStack_7055_);
                                crate::leanh::lean_inc(v_cmdPos_7054_);
                                crate::leanh::lean_inc(v_currRecDepth_7053_);
                                crate::leanh::lean_inc_ref(v_fileMap_7052_);
                                crate::leanh::lean_inc_ref(v_fileName_7051_);
                                v___x_7091_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                                crate::leanh::lean_ctor_set(v___x_7091_, 0, v_fileName_7051_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 1, v_fileMap_7052_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 2, v_currRecDepth_7053_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 3, v_cmdPos_7054_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 4, v_macroStack_7055_);
                                crate::leanh::lean_ctor_set(
                                    v___x_7091_,
                                    5,
                                    v_quotContext_x3f_7056_,
                                );
                                crate::leanh::lean_ctor_set(v___x_7091_, 6, v_currMacroScope_7057_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 7, v_ref_7090_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 8, v_snap_x3f_7058_);
                                crate::leanh::lean_ctor_set(v___x_7091_, 9, v_cancelTk_x3f_7059_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v___x_7091_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10)
                                        as u32,
                                    v_suppressElabErrors_7060_,
                                );
                                v___x_7092_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
                                v___x_7093_ = l_Lean_Environment_contains(
                                    v_env_7061_,
                                    v___x_7092_,
                                    v___x_7019_,
                                );
                                if v___x_7093_ == 0 {
                                    crate::leanh::lean_dec(v_t_7064_);
                                    crate::leanh::lean_dec(v_id_6978_);
                                    v___x_7094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
                                    v___x_7095_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v___x_7094_, v___x_7091_, v_a_6918_);
                                    crate::leanh::lean_dec_ref_known(v___x_7091_, 10);
                                    return v___x_7095_;
                                } else {
                                    v___y_7066_ = v___x_7091_;
                                    v___y_7067_ = v_a_6918_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_id_6978_);
                                crate::leanh::lean_dec(v_x_6916_);
                                v_a_7096_ = crate::leanh::lean_ctor_get(v___x_7048_, 0);
                                v_isSharedCheck_7103_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7048_)) as u8;
                                if v_isSharedCheck_7103_ == 0 {
                                    v___x_7098_ = v___x_7048_;
                                    v_isShared_7099_ = v_isSharedCheck_7103_;
                                    state = 14;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7096_);
                                    crate::leanh::lean_dec(v___x_7048_);
                                    v___x_7098_ = crate::leanh::lean_box(0);
                                    v_isShared_7099_ = v_isSharedCheck_7103_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_dec_ref(v___y_6925_);
                v___x_6928_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_6926_);
                v_a_6929_ = crate::leanh::lean_ctor_get(v___x_6928_, 0);
                v_isSharedCheck_6968_ = (!crate::leanh::lean_is_exclusive(v___x_6928_)) as u8;
                if v_isSharedCheck_6968_ == 0 {
                    v___x_6931_ = v___x_6928_;
                    v_isShared_6932_ = v_isSharedCheck_6968_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6929_);
                    crate::leanh::lean_dec(v___x_6928_);
                    v___x_6931_ = crate::leanh::lean_box(0);
                    v_isShared_6932_ = v_isSharedCheck_6968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6933_ = lean_st_ref_take(v___y_6926_);
                v_env_6934_ = crate::leanh::lean_ctor_get(v___x_6933_, 0);
                v_messages_6935_ = crate::leanh::lean_ctor_get(v___x_6933_, 1);
                v_scopes_6936_ = crate::leanh::lean_ctor_get(v___x_6933_, 2);
                v_usedQuotCtxts_6937_ = crate::leanh::lean_ctor_get(v___x_6933_, 3);
                v_nextMacroScope_6938_ = crate::leanh::lean_ctor_get(v___x_6933_, 4);
                v_maxRecDepth_6939_ = crate::leanh::lean_ctor_get(v___x_6933_, 5);
                v_ngen_6940_ = crate::leanh::lean_ctor_get(v___x_6933_, 6);
                v_auxDeclNGen_6941_ = crate::leanh::lean_ctor_get(v___x_6933_, 7);
                v_infoState_6942_ = crate::leanh::lean_ctor_get(v___x_6933_, 8);
                v_traceState_6943_ = crate::leanh::lean_ctor_get(v___x_6933_, 9);
                v_snapshotTasks_6944_ = crate::leanh::lean_ctor_get(v___x_6933_, 10);
                v_isSharedCheck_6967_ = (!crate::leanh::lean_is_exclusive(v___x_6933_)) as u8;
                if v_isSharedCheck_6967_ == 0 {
                    v___x_6946_ = v___x_6933_;
                    v_isShared_6947_ = v_isSharedCheck_6967_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6944_);
                    crate::leanh::lean_inc(v_traceState_6943_);
                    crate::leanh::lean_inc(v_infoState_6942_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6941_);
                    crate::leanh::lean_inc(v_ngen_6940_);
                    crate::leanh::lean_inc(v_maxRecDepth_6939_);
                    crate::leanh::lean_inc(v_nextMacroScope_6938_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_6937_);
                    crate::leanh::lean_inc(v_scopes_6936_);
                    crate::leanh::lean_inc(v_messages_6935_);
                    crate::leanh::lean_inc(v_env_6934_);
                    crate::leanh::lean_dec(v___x_6933_);
                    v___x_6946_ = crate::leanh::lean_box(0);
                    v_isShared_6947_ = v_isSharedCheck_6967_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6948_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_6949_ = crate::leanh::lean_ctor_get(v___x_6948_, 0);
                v_asyncMode_6950_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6949_, 2);
                v___x_6951_ = l_Lean_DeclarationRange_ofStringPositions(
                    v___y_6921_,
                    v___y_6923_,
                    v___y_6927_,
                );
                crate::leanh::lean_dec(v___y_6927_);
                crate::leanh::lean_dec(v___y_6923_);
                v___x_6952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6952_, 0, v_a_6929_);
                crate::leanh::lean_ctor_set(v___x_6952_, 1, v___x_6951_);
                v___x_6953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6953_, 0, v___x_6952_);
                v___x_6954_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                v___x_6955_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6955_, 0, v___x_6954_);
                crate::leanh::lean_ctor_set(v___x_6955_, 1, v___y_6922_);
                crate::leanh::lean_ctor_set(v___x_6955_, 2, v___x_6953_);
                v___x_6956_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6956_, 0, v___y_6924_);
                crate::leanh::lean_ctor_set(v___x_6956_, 1, v___x_6955_);
                v___x_6957_ = crate::leanh::lean_box(0);
                v___x_6958_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6948_,
                    v_env_6934_,
                    v___x_6956_,
                    v_asyncMode_6950_,
                    v___x_6957_,
                );
                if v_isShared_6947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6946_, 0, v___x_6958_);
                    v___x_6960_ = v___x_6946_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6966_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 0, v___x_6958_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 1, v_messages_6935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 2, v_scopes_6936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 3, v_usedQuotCtxts_6937_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 4, v_nextMacroScope_6938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 5, v_maxRecDepth_6939_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 6, v_ngen_6940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 7, v_auxDeclNGen_6941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 8, v_infoState_6942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 9, v_traceState_6943_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6966_, 10, v_snapshotTasks_6944_);
                    v___x_6960_ = v_reuseFailAlloc_6966_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6961_ = lean_st_ref_set(v___y_6926_, v___x_6960_);
                v___x_6962_ = crate::leanh::lean_box(0);
                if v_isShared_6932_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6931_, 0, v___x_6962_);
                    v___x_6964_ = v___x_6931_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6965_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6965_, 0, v___x_6962_);
                    v___x_6964_ = v_reuseFailAlloc_6965_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6964_;
            }
            6 => {
                v___x_6987_ = l_Lean_Syntax_getTailPos_x3f(v_id_6978_, v___y_6981_);
                crate::leanh::lean_dec(v_id_6978_);
                if crate::leanh::lean_obj_tag(v___x_6987_) == 0 {
                    crate::leanh::lean_inc(v___y_6986_);
                    v___y_6921_ = v___y_6980_;
                    v___y_6922_ = v___y_6982_;
                    v___y_6923_ = v___y_6986_;
                    v___y_6924_ = v___y_6983_;
                    v___y_6925_ = v___y_6984_;
                    v___y_6926_ = v___y_6985_;
                    v___y_6927_ = v___y_6986_;
                    state = 1;
                    continue;
                } else {
                    v_val_6988_ = crate::leanh::lean_ctor_get(v___x_6987_, 0);
                    crate::leanh::lean_inc(v_val_6988_);
                    crate::leanh::lean_dec_ref_known(v___x_6987_, 1);
                    v___y_6921_ = v___y_6980_;
                    v___y_6922_ = v___y_6982_;
                    v___y_6923_ = v___y_6986_;
                    v___y_6924_ = v___y_6983_;
                    v___y_6925_ = v___y_6984_;
                    v___y_6926_ = v___y_6985_;
                    v___y_6927_ = v_val_6988_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v_fileMap_6994_ = crate::leanh::lean_ctor_get(v___y_6992_, 1);
                crate::leanh::lean_inc_ref(v_fileMap_6994_);
                v___x_6995_ = 0;
                v___x_6996_ = l_Lean_Syntax_getPos_x3f(v_id_6978_, v___x_6995_);
                if crate::leanh::lean_obj_tag(v___x_6996_) == 0 {
                    v___y_6980_ = v_fileMap_6994_;
                    v___y_6981_ = v___x_6995_;
                    v___y_6982_ = v___y_6990_;
                    v___y_6983_ = v___y_6991_;
                    v___y_6984_ = v___y_6992_;
                    v___y_6985_ = v___y_6993_;
                    v___y_6986_ = v___x_6972_;
                    state = 6;
                    continue;
                } else {
                    v_val_6997_ = crate::leanh::lean_ctor_get(v___x_6996_, 0);
                    crate::leanh::lean_inc(v_val_6997_);
                    crate::leanh::lean_dec_ref_known(v___x_6996_, 1);
                    v___y_6980_ = v_fileMap_6994_;
                    v___y_6981_ = v___x_6995_;
                    v___y_6982_ = v___y_6990_;
                    v___y_6983_ = v___y_6991_;
                    v___y_6984_ = v___y_6992_;
                    v___y_6985_ = v___y_6993_;
                    v___y_6986_ = v_val_6997_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_7003_ = lean_st_ref_get(v___y_7002_);
                v_env_7004_ = crate::leanh::lean_ctor_get(v___x_7003_, 0);
                crate::leanh::lean_inc_ref(v_env_7004_);
                crate::leanh::lean_dec(v___x_7003_);
                v___x_7005_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_7006_ = crate::leanh::lean_ctor_get(v___x_7005_, 0);
                v_asyncMode_7007_ = crate::leanh::lean_ctor_get(v_toEnvExtension_7006_, 2);
                v___x_7008_ = crate::leanh::lean_box(1);
                v___x_7009_ = crate::leanh::lean_box(0);
                v___x_7010_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_7008_,
                    v___x_7005_,
                    v_env_7004_,
                    v_asyncMode_7007_,
                    v___x_7009_,
                );
                v___x_7011_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_7000_, v___x_7010_);
                crate::leanh::lean_dec(v___x_7010_);
                if v___x_7011_ == 0 {
                    v___y_6990_ = v___y_6999_;
                    v___y_6991_ = v___y_7000_;
                    v___y_6992_ = v___y_7001_;
                    v___y_6993_ = v___y_7002_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6999_);
                    v___x_7012_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
                    v___x_7013_ = l_Lean_MessageData_ofName(v___y_7000_);
                    v___x_7014_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7014_, 0, v___x_7012_);
                    crate::leanh::lean_ctor_set(v___x_7014_, 1, v___x_7013_);
                    v___x_7015_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
                    v___x_7016_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7016_, 0, v___x_7014_);
                    crate::leanh::lean_ctor_set(v___x_7016_, 1, v___x_7015_);
                    v___x_7017_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7016_, v___y_7001_, v___y_7002_);
                    crate::leanh::lean_dec_ref(v___y_7001_);
                    crate::leanh::lean_dec(v_id_6978_);
                    return v___x_7017_;
                }
            }
            9 => {
                v___x_7025_ = l_Lean_Name_getNumParts(v___y_7022_);
                v___x_7026_ = lean_nat_dec_eq(v___x_7025_, v___x_6977_);
                crate::leanh::lean_dec(v___x_7025_);
                if v___x_7026_ == 0 {
                    if v___x_7019_ == 0 {
                        v___y_6999_ = v___y_7021_;
                        v___y_7000_ = v___y_7022_;
                        v___y_7001_ = v___y_7023_;
                        v___y_7002_ = v___y_7024_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_7021_);
                        v___x_7027_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
                        v___x_7028_ = l_Lean_MessageData_ofName(v___y_7022_);
                        v___x_7029_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7029_, 0, v___x_7027_);
                        crate::leanh::lean_ctor_set(v___x_7029_, 1, v___x_7028_);
                        v___x_7030_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
                        v___x_7031_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7031_, 0, v___x_7029_);
                        crate::leanh::lean_ctor_set(v___x_7031_, 1, v___x_7030_);
                        v___x_7032_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
                        v___x_7033_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_7033_, 0, v___x_7031_);
                        crate::leanh::lean_ctor_set(v___x_7033_, 1, v___x_7032_);
                        v___x_7034_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7033_, v___y_7023_, v___y_7024_);
                        crate::leanh::lean_dec_ref(v___y_7023_);
                        crate::leanh::lean_dec(v_id_6978_);
                        return v___x_7034_;
                    }
                } else {
                    v___y_6999_ = v___y_7021_;
                    v___y_7000_ = v___y_7022_;
                    v___y_7001_ = v___y_7023_;
                    v___y_7002_ = v___y_7024_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                v___x_7040_ = l_Lean_Name_hasMacroScopes(v___y_7037_);
                if v___x_7040_ == 0 {
                    v___y_7021_ = v___y_7036_;
                    v___y_7022_ = v___y_7037_;
                    v___y_7023_ = v___y_7038_;
                    v___y_7024_ = v___y_7039_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_7037_);
                    crate::leanh::lean_dec_ref(v___y_7036_);
                    v___x_7041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
                    crate::leanh::lean_inc(v_id_6978_);
                    v___x_7042_ = l_Lean_MessageData_ofSyntax(v_id_6978_);
                    v___x_7043_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7043_, 0, v___x_7041_);
                    crate::leanh::lean_ctor_set(v___x_7043_, 1, v___x_7042_);
                    v___x_7044_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
                    v___x_7045_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7045_, 0, v___x_7043_);
                    crate::leanh::lean_ctor_set(v___x_7045_, 1, v___x_7044_);
                    v___x_7046_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7045_, v___y_7038_, v___y_7039_);
                    crate::leanh::lean_dec_ref(v___y_7038_);
                    crate::leanh::lean_dec(v_id_6978_);
                    return v___x_7046_;
                }
            }
            11 => {
                v___x_7068_ =
                    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
                v___x_7069_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_7068_, v___x_7019_, v___y_7066_, v___y_7067_);
                if crate::leanh::lean_obj_tag(v___x_7069_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7069_, 1);
                    v___x_7070_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
                    v___f_7071_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    crate::leanh::lean_closure_set(v___f_7071_, 0, v_t_7064_);
                    crate::leanh::lean_closure_set(v___f_7071_, 1, v___x_7070_);
                    v___x_7072_ = l_Lean_Elab_Command_runTermElabM___redArg(
                        v___f_7071_,
                        v___y_7066_,
                        v___y_7067_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7072_) == 0 {
                        v_a_7073_ = crate::leanh::lean_ctor_get(v___x_7072_, 0);
                        crate::leanh::lean_inc(v_a_7073_);
                        crate::leanh::lean_dec_ref_known(v___x_7072_, 1);
                        v___x_7074_ = l_Lean_TSyntax_getId(v_id_6978_);
                        v___x_7075_ = l_Lean_Name_isAnonymous(v___x_7074_);
                        if v___x_7075_ == 0 {
                            v___y_7036_ = v_a_7073_;
                            v___y_7037_ = v___x_7074_;
                            v___y_7038_ = v___y_7066_;
                            v___y_7039_ = v___y_7067_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_7074_);
                            crate::leanh::lean_dec(v_a_7073_);
                            v___x_7076_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
                            crate::leanh::lean_inc(v_id_6978_);
                            v___x_7077_ = l_Lean_MessageData_ofSyntax(v_id_6978_);
                            v___x_7078_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7078_, 0, v___x_7076_);
                            crate::leanh::lean_ctor_set(v___x_7078_, 1, v___x_7077_);
                            v___x_7079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
                            v___x_7080_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7080_, 0, v___x_7078_);
                            crate::leanh::lean_ctor_set(v___x_7080_, 1, v___x_7079_);
                            v___x_7081_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7080_, v___y_7066_, v___y_7067_);
                            crate::leanh::lean_dec_ref(v___y_7066_);
                            crate::leanh::lean_dec(v_id_6978_);
                            return v___x_7081_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_7066_);
                        crate::leanh::lean_dec(v_id_6978_);
                        v_a_7082_ = crate::leanh::lean_ctor_get(v___x_7072_, 0);
                        v_isSharedCheck_7089_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7072_)) as u8;
                        if v_isSharedCheck_7089_ == 0 {
                            v___x_7084_ = v___x_7072_;
                            v_isShared_7085_ = v_isSharedCheck_7089_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7082_);
                            crate::leanh::lean_dec(v___x_7072_);
                            v___x_7084_ = crate::leanh::lean_box(0);
                            v_isShared_7085_ = v_isSharedCheck_7089_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_7066_);
                    crate::leanh::lean_dec(v_t_7064_);
                    crate::leanh::lean_dec(v_id_6978_);
                    return v___x_7069_;
                }
            }
            12 => {
                if v_isShared_7085_ == 0 {
                    v___x_7087_ = v___x_7084_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7088_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7088_, 0, v_a_7082_);
                    v___x_7087_ = v_reuseFailAlloc_7088_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7087_;
            }
            14 => {
                if v_isShared_7099_ == 0 {
                    v___x_7101_ = v___x_7098_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7102_, 0, v_a_7096_);
                    v___x_7101_ = v_reuseFailAlloc_7102_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7101_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed(
    mut v_x_7104_: *mut crate::leanh::LeanObject,
    mut v_a_7105_: *mut crate::leanh::LeanObject,
    mut v_a_7106_: *mut crate::leanh::LeanObject,
    mut v_a_7107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7108_ =
        l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_7104_, v_a_7105_, v_a_7106_);
    crate::leanh::lean_dec(v_a_7106_);
    crate::leanh::lean_dec_ref(v_a_7105_);
    return v_res_7108_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(
    mut v_00_u03b1_7109_: *mut crate::leanh::LeanObject,
    mut v_ref_7110_: *mut crate::leanh::LeanObject,
    mut v_msg_7111_: *mut crate::leanh::LeanObject,
    mut v___y_7112_: *mut crate::leanh::LeanObject,
    mut v___y_7113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7115_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_7110_, v_msg_7111_, v___y_7112_, v___y_7113_);
    return v___x_7115_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(
    mut v_00_u03b1_7116_: *mut crate::leanh::LeanObject,
    mut v_ref_7117_: *mut crate::leanh::LeanObject,
    mut v_msg_7118_: *mut crate::leanh::LeanObject,
    mut v___y_7119_: *mut crate::leanh::LeanObject,
    mut v___y_7120_: *mut crate::leanh::LeanObject,
    mut v___y_7121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7122_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v_00_u03b1_7116_, v_ref_7117_, v_msg_7118_, v___y_7119_, v___y_7120_);
    crate::leanh::lean_dec(v___y_7120_);
    crate::leanh::lean_dec_ref(v___y_7119_);
    crate::leanh::lean_dec(v_ref_7117_);
    return v_res_7122_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(
    mut v_msgData_7123_: *mut crate::leanh::LeanObject,
    mut v___y_7124_: *mut crate::leanh::LeanObject,
    mut v___y_7125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7127_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_7123_, v___y_7125_);
    return v___x_7127_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(
    mut v_msgData_7128_: *mut crate::leanh::LeanObject,
    mut v___y_7129_: *mut crate::leanh::LeanObject,
    mut v___y_7130_: *mut crate::leanh::LeanObject,
    mut v___y_7131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7132_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(v_msgData_7128_, v___y_7129_, v___y_7130_);
    crate::leanh::lean_dec(v___y_7130_);
    crate::leanh::lean_dec_ref(v___y_7129_);
    return v_res_7132_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(
    mut v_00_u03b1_7133_: *mut crate::leanh::LeanObject,
    mut v_msg_7134_: *mut crate::leanh::LeanObject,
    mut v___y_7135_: *mut crate::leanh::LeanObject,
    mut v___y_7136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7138_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_7134_, v___y_7135_, v___y_7136_);
    return v___x_7138_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(
    mut v_00_u03b1_7139_: *mut crate::leanh::LeanObject,
    mut v_msg_7140_: *mut crate::leanh::LeanObject,
    mut v___y_7141_: *mut crate::leanh::LeanObject,
    mut v___y_7142_: *mut crate::leanh::LeanObject,
    mut v___y_7143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7144_ =
        l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(
            v_00_u03b1_7139_,
            v_msg_7140_,
            v___y_7141_,
            v___y_7142_,
        );
    crate::leanh::lean_dec(v___y_7142_);
    crate::leanh::lean_dec_ref(v___y_7141_);
    return v_res_7144_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(
    mut v_msgData_7145_: *mut crate::leanh::LeanObject,
    mut v_macroStack_7146_: *mut crate::leanh::LeanObject,
    mut v___y_7147_: *mut crate::leanh::LeanObject,
    mut v___y_7148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7150_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_7145_, v_macroStack_7146_, v___y_7148_);
    return v___x_7150_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(
    mut v_msgData_7151_: *mut crate::leanh::LeanObject,
    mut v_macroStack_7152_: *mut crate::leanh::LeanObject,
    mut v___y_7153_: *mut crate::leanh::LeanObject,
    mut v___y_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7156_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(v_msgData_7151_, v_macroStack_7152_, v___y_7153_, v___y_7154_);
    crate::leanh::lean_dec(v___y_7154_);
    crate::leanh::lean_dec_ref(v___y_7153_);
    return v_res_7156_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7164_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_7165_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
    v___x_7166_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1;
    v___x_7167_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_7168_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7164_,
        v___x_7165_,
        v___x_7166_,
        v___x_7167_,
    );
    return v___x_7168_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___boxed(
    mut v_a_7169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7170_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
    return v_res_7170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ErrorExplanation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap =
        _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap();
    crate::leanh::lean_mark_persistent(
        l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap,
    );
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ErrorExplanation(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ErrorExplanation(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_UserWidget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Widget_UserWidget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorExplanation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ErrorExplanation(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ErrorExplanation(builtin);
}
