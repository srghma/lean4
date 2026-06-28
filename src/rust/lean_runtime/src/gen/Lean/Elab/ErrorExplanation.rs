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
    meta_initialize_Lean_Widget_UserWidget, runtime_initialize_Lean_Widget_UserWidget,
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_float, lean_ctor_set_tag, lean_ctor_set_uint8, lean_ctor_set_uint64,
    lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [101, 114, 114, 111, 114, 68, 101, 115, 99, 114, 105, 112, 116, 105, 111, 110, 87, 105, 100, 103, 101, 116, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__1_value) as *mut LeanObject,11821295174094476641 as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value: LeanStringObject<
    7,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value: LeanCtorObject<3> =
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
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__2_value
            ) as *mut LeanObject,
            7097802073468323731 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value: LeanStringObject<
    23,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value: LeanCtorObject<3> =
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
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__4_value
            ) as *mut LeanObject,
            3360895518896177531 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value: LeanStringObject<
    19,
> = LeanStringObject {
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 77, 97, 99, 114, 111, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value: LeanCtorObject<3> =
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
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__6_value
            ) as *mut LeanObject,
            9653194137920487497 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value: LeanCtorObject<3> =
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
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value_aux_2
            ) as *mut LeanObject,
            core::ptr::addr_of!(
                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__8_value
            ) as *mut LeanObject,
            12924865489819135822 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__10_value)
            as *mut LeanObject,
        13287924405428050690 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value: LeanStringObject<
    23,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__12_value)
            as *mut LeanObject,
        16765905629307186191 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value: LeanStringObject<
    20,
> = LeanStringObject {
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
        105, 110, 116, 101, 114, 112, 111, 108, 97, 116, 101, 100, 83, 116, 114, 75, 105, 110, 100,
        0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__14_value)
            as *mut LeanObject,
        14298422259736409839 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value: LeanStringObject<
    4,
> = LeanStringObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__16_value)
            as *mut LeanObject,
        12966880221525079621 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value: LeanStringObject<
    23,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110, 103, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__20_value)
            as *mut LeanObject,
        17497790286802646181 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__22_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value: LeanStringObject<
    5,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__24_value)
            as *mut LeanObject,
        9855511589286918680 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value: LeanStringObject<
    11,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_1: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_2: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__1_value)
            as *mut LeanObject,
        16572064140653406795 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__26_value)
            as *mut LeanObject,
        9368229134555052249 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value: LeanStringObject<
    2,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value: LeanStringObject<
    8,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__30_value)
            as *mut LeanObject,
        13317951319906582257 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value: LeanStringObject<
    3,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        108, 111, 103, 78, 97, 109, 101, 100, 87, 97, 114, 110, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__35_value)
            as *mut LeanObject,
        17298265491216151842 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__37_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__41_value)
            as *mut LeanObject,
        6024285242114364631 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__43_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value: LeanStringObject<
    19,
> = LeanStringObject {
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
        76, 101, 97, 110, 46, 108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value: LeanStringObject<
    14,
> = LeanStringObject {
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
        108, 111, 103, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__47_value)
            as *mut LeanObject,
        14450959914897649857 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__49_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value: LeanStringObject<
    23,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value: LeanStringObject<
    18,
> = LeanStringObject {
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
        116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 65, 116, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__53_value)
            as *mut LeanObject,
        8567430786828469655 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__55_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value: LeanStringObject<
    6,
> = LeanStringObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__57_value)
            as *mut LeanObject,
        5117844058249666356 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value: LeanStringObject<
    16,
> = LeanStringObject {
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
        116, 104, 114, 111, 119, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__61_value)
            as *mut LeanObject,
        8906461912520152887 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64_value: LeanCtorObject<
    2,
> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__63_value)
            as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64_value)
        as *mut LeanObject;
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0: u64 = 0;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [69, 120, 99, 101, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__0_value) as *mut LeanObject,16971822718086795385 as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__2_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__1_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__4_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [76, 111, 103, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__6_value) as *mut LeanObject,15983123899464659095 as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__8_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__10_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__12_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__7_value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__14_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__15_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__13_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__16_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__11_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__17_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__9_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__18_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__5_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__19_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__3_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__20_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21_value) as *mut LeanObject;
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2_value) as *mut LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value) as *mut LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__7_value) as *mut LeanObject,7870113334857981723 as *mut LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17_value) as *mut LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__20_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__22_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0_value) as *mut LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1_value) as *mut LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value: LeanStringObject<16> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value) as *mut LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__1_value) as *mut LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2: *mut LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2_value) as *mut LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value: LeanStringObject<25> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__0_value) as *mut LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value: LeanStringObject<158> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2_value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__2_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__3_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5_value: LeanStringObject<20> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5_value) as *mut LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__6_value) as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0_value: LeanStringObject<
    17,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2_value: LeanStringObject<
    31,
> = LeanStringObject {
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
        96, 32, 119, 97, 115, 32, 114, 101, 109, 111, 118, 101, 100, 32, 105, 110, 32, 76, 101, 97,
        110, 32, 118, 101, 114, 115, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4_value: LeanStringObject<
    25,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6_value: LeanStringObject<
    51,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8_value: LeanStringObject<
    81,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10_value: LeanStringObject<
    15,
> = LeanStringObject {
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
        84, 104, 101, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12_value: LeanStringObject<
    24,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14_value: LeanStringObject<
    13,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16_value: LeanStringObject<
    42,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value: LeanStringObject<17> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 67, 104, 101, 99, 107, 101, 100, 78, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value) as *mut LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut LeanObject,13311307985783427614 as *mut LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__1_value) as *mut LeanObject,5305096624820345885 as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2_value) as *mut LeanObject;
static mut l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value:
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
    m_data: [67, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value:
    LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__0_value)
            as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__0_value
        ) as *mut LeanObject,
        17342580262104060118 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__1_value
        ) as *mut LeanObject,
        18241697017225771414 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value:
    LeanStringObject<66> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_value:
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
        73, 110, 118, 97, 108, 105, 100, 32, 110, 97, 109, 101, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_value:
    LeanStringObject<52> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_value:
    LeanStringObject<149> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_value:
    LeanStringObject<132> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value:
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
    m_data: [77, 101, 116, 97, 100, 97, 116, 97, 0],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value
)
    as *mut LeanObject;
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut LeanObject,18239673213070638308 as *mut LeanObject] };
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value:
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
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__15_value
        ) as *mut LeanObject,
        16597581185784988388 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_value:
    LeanStringObject<38> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_value:
    LeanStringObject<83> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [101, 108, 97, 98, 82, 101, 103, 105, 115, 116, 101, 114, 69, 114, 114, 111, 114, 69, 120, 112, 108, 97, 110, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__0_value) as *mut LeanObject,13311307985783427614 as *mut LeanObject] };
pub static l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__0_value) as *mut LeanObject,2761648309649773589 as *mut LeanObject] };
static mut l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1()
-> *mut LeanObject {
    let mut v___x_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut LeanObject = core::ptr::null_mut();
    v___x_3592_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___closed__2;
    v___x_3593_ = l_Lean_errorDescriptionWidget;
    v___x_3594_ = l_Lean_Widget_addBuiltinModule(v___x_3592_, v___x_3593_);
    return v___x_3594_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1___boxed(
    mut v_a_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3596_: *mut LeanObject = core::ptr::null_mut();
    v_res_3596_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
    return v_res_3596_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19()
-> *mut LeanObject {
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    v___x_3645_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__18;
    v___x_3646_ = l_String_toRawSubstring_x27(v___x_3645_);
    return v___x_3646_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34()
-> *mut LeanObject {
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    v___x_3674_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__33;
    v___x_3675_ = l_String_toRawSubstring_x27(v___x_3674_);
    return v___x_3675_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40()
-> *mut LeanObject {
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    v___x_3687_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__39;
    v___x_3688_ = l_String_toRawSubstring_x27(v___x_3687_);
    return v___x_3688_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46()
-> *mut LeanObject {
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3701_: *mut LeanObject = core::ptr::null_mut();
    v___x_3700_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__45;
    v___x_3701_ = l_String_toRawSubstring_x27(v___x_3700_);
    return v___x_3701_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52()
-> *mut LeanObject {
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    v___x_3713_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__51;
    v___x_3714_ = l_String_toRawSubstring_x27(v___x_3713_);
    return v___x_3714_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60()
-> *mut LeanObject {
    let mut v___x_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut LeanObject = core::ptr::null_mut();
    v___x_3729_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__59;
    v___x_3730_ = l_String_toRawSubstring_x27(v___x_3729_);
    return v___x_3730_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(
    mut v_x_3741_: *mut LeanObject,
    mut v_a_3742_: *mut LeanObject,
    mut v_a_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: u8 = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: u8 = 0;
    let mut v___x_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    let mut v___x_3754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: u8 = 0;
    let mut v___x_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: u8 = 0;
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: u8 = 0;
    let mut v_quotContext_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: u8 = 0;
    let mut v___x_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: u8 = 0;
    let mut v_quotContext_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: u8 = 0;
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: u8 = 0;
    let mut v_quotContext_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: u8 = 0;
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: u8 = 0;
    let mut v_quotContext_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v_quotContext_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: u8 = 0;
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: u8 = 0;
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: u8 = 0;
    let mut v_quotContext_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: u8 = 0;
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3744_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
                lean_inc(v_x_3741_);
                v___x_3745_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3744_);
                if v___x_3745_ == 0 {
                    v___x_3746_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
                    lean_inc(v_x_3741_);
                    v___x_3747_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3746_);
                    if v___x_3747_ == 0 {
                        v___x_3748_ =
                            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
                        lean_inc(v_x_3741_);
                        v___x_3749_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3748_);
                        if v___x_3749_ == 0 {
                            v___x_3750_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
                            lean_inc(v_x_3741_);
                            v___x_3751_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3750_);
                            if v___x_3751_ == 0 {
                                v___x_3752_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
                                lean_inc(v_x_3741_);
                                v___x_3753_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3752_);
                                if v___x_3753_ == 0 {
                                    v___x_3754_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
                                    lean_inc(v_x_3741_);
                                    v___x_3755_ = l_Lean_Syntax_isOfKind(v_x_3741_, v___x_3754_);
                                    if v___x_3755_ == 0 {
                                        lean_dec(v_x_3741_);
                                        v___x_3756_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                        return v___x_3756_;
                                    } else {
                                        v___x_3757_ = lean_unsigned_to_nat(0);
                                        v___x_3758_ = lean_unsigned_to_nat(3);
                                        v___x_3759_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3758_);
                                        v___x_3760_ =
                                            l_Lean_Syntax_matchesNull(v___x_3759_, v___x_3757_);
                                        if v___x_3760_ == 0 {
                                            lean_dec(v_x_3741_);
                                            v___x_3761_ =
                                                l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                            return v___x_3761_;
                                        } else {
                                            v___x_3762_ = lean_unsigned_to_nat(1);
                                            v___x_3763_ =
                                                l_Lean_Syntax_getArg(v_x_3741_, v___x_3762_);
                                            v___x_3764_ = lean_unsigned_to_nat(2);
                                            v_id_3765_ =
                                                l_Lean_Syntax_getArg(v_x_3741_, v___x_3764_);
                                            v___x_3766_ = lean_unsigned_to_nat(4);
                                            v___x_3767_ =
                                                l_Lean_Syntax_getArg(v_x_3741_, v___x_3766_);
                                            lean_dec(v_x_3741_);
                                            v___x_3768_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                            lean_inc(v___x_3767_);
                                            v___x_3769_ =
                                                l_Lean_Syntax_isOfKind(v___x_3767_, v___x_3768_);
                                            if v___x_3769_ == 0 {
                                                v_quotContext_3770_ = lean_ctor_get(v_a_3742_, 1);
                                                v_currMacroScope_3771_ =
                                                    lean_ctor_get(v_a_3742_, 2);
                                                v_ref_3772_ = lean_ctor_get(v_a_3742_, 5);
                                                v___x_3773_ = l_Lean_SourceInfo_fromRef(
                                                    v_ref_3772_,
                                                    v___x_3769_,
                                                );
                                                v___x_3774_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                                v___x_3775_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
                                                v___x_3776_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
                                                lean_inc(v_currMacroScope_3771_);
                                                lean_inc(v_quotContext_3770_);
                                                v___x_3777_ = l_Lean_addMacroScope(
                                                    v_quotContext_3770_,
                                                    v___x_3776_,
                                                    v_currMacroScope_3771_,
                                                );
                                                v___x_3778_ = lean_box(0);
                                                v___x_3779_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
                                                lean_inc(v___x_3773_);
                                                v___x_3780_ = lean_alloc_ctor(3, 4, (0) as u32);
                                                lean_ctor_set(v___x_3780_, 0, v___x_3773_);
                                                lean_ctor_set(v___x_3780_, 1, v___x_3775_);
                                                lean_ctor_set(v___x_3780_, 2, v___x_3777_);
                                                lean_ctor_set(v___x_3780_, 3, v___x_3779_);
                                                v___x_3781_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                                v___x_3787_ = l_Lean_TSyntax_getId(v_id_3765_);
                                                lean_dec(v_id_3765_);
                                                lean_inc(v___x_3787_);
                                                v___x_3788_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3778_, v___x_3787_);
                                                if lean_obj_tag(v___x_3788_) == 0 {
                                                    v___x_3789_ = l_Lean_quoteNameMk(v___x_3787_);
                                                    v___y_3783_ = v___x_3789_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    lean_dec(v___x_3787_);
                                                    v_val_3790_ = lean_ctor_get(v___x_3788_, 0);
                                                    lean_inc(v_val_3790_);
                                                    lean_dec_ref_known(v___x_3788_, 1);
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
                                                    lean_dec_ref(v___x_3794_);
                                                    v___x_3796_ = lean_box(2);
                                                    v___x_3797_ = l_Lean_Syntax_mkNameLit(
                                                        v___x_3795_,
                                                        v___x_3796_,
                                                    );
                                                    v___x_3798_ = lean_mk_empty_array_with_capacity(
                                                        v___x_3762_,
                                                    );
                                                    v___x_3799_ =
                                                        lean_array_push(v___x_3798_, v___x_3797_);
                                                    v___x_3800_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                    lean_ctor_set(v___x_3800_, 0, v___x_3796_);
                                                    lean_ctor_set(v___x_3800_, 1, v___x_3791_);
                                                    lean_ctor_set(v___x_3800_, 2, v___x_3799_);
                                                    v___y_3783_ = v___x_3800_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                v_quotContext_3801_ = lean_ctor_get(v_a_3742_, 1);
                                                v_currMacroScope_3802_ =
                                                    lean_ctor_get(v_a_3742_, 2);
                                                v_ref_3803_ = lean_ctor_get(v_a_3742_, 5);
                                                v___x_3804_ = l_Lean_SourceInfo_fromRef(
                                                    v_ref_3803_,
                                                    v___x_3753_,
                                                );
                                                v___x_3805_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                                v___x_3806_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__19);
                                                v___x_3807_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__21;
                                                lean_inc(v_currMacroScope_3802_);
                                                lean_inc(v_quotContext_3801_);
                                                v___x_3808_ = l_Lean_addMacroScope(
                                                    v_quotContext_3801_,
                                                    v___x_3807_,
                                                    v_currMacroScope_3802_,
                                                );
                                                v___x_3809_ = lean_box(0);
                                                v___x_3810_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__23;
                                                lean_inc(v___x_3804_);
                                                v___x_3811_ = lean_alloc_ctor(3, 4, (0) as u32);
                                                lean_ctor_set(v___x_3811_, 0, v___x_3804_);
                                                lean_ctor_set(v___x_3811_, 1, v___x_3806_);
                                                lean_ctor_set(v___x_3811_, 2, v___x_3808_);
                                                lean_ctor_set(v___x_3811_, 3, v___x_3810_);
                                                v___x_3812_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                                v___x_3822_ = l_Lean_TSyntax_getId(v_id_3765_);
                                                lean_dec(v_id_3765_);
                                                lean_inc(v___x_3822_);
                                                v___x_3823_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3809_, v___x_3822_);
                                                if lean_obj_tag(v___x_3823_) == 0 {
                                                    v___x_3824_ = l_Lean_quoteNameMk(v___x_3822_);
                                                    v___y_3814_ = v___x_3824_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    lean_dec(v___x_3822_);
                                                    v_val_3825_ = lean_ctor_get(v___x_3823_, 0);
                                                    lean_inc(v_val_3825_);
                                                    lean_dec_ref_known(v___x_3823_, 1);
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
                                                    lean_dec_ref(v___x_3829_);
                                                    v___x_3831_ = lean_box(2);
                                                    v___x_3832_ = l_Lean_Syntax_mkNameLit(
                                                        v___x_3830_,
                                                        v___x_3831_,
                                                    );
                                                    v___x_3833_ = lean_mk_empty_array_with_capacity(
                                                        v___x_3762_,
                                                    );
                                                    v___x_3834_ =
                                                        lean_array_push(v___x_3833_, v___x_3832_);
                                                    v___x_3835_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                    lean_ctor_set(v___x_3835_, 0, v___x_3831_);
                                                    lean_ctor_set(v___x_3835_, 1, v___x_3826_);
                                                    lean_ctor_set(v___x_3835_, 2, v___x_3834_);
                                                    v___y_3814_ = v___x_3835_;
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___x_3836_ = lean_unsigned_to_nat(0);
                                    v___x_3837_ = lean_unsigned_to_nat(2);
                                    v___x_3838_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3837_);
                                    v___x_3839_ =
                                        l_Lean_Syntax_matchesNull(v___x_3838_, v___x_3836_);
                                    if v___x_3839_ == 0 {
                                        lean_dec(v_x_3741_);
                                        v___x_3840_ =
                                            l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                        return v___x_3840_;
                                    } else {
                                        v___x_3841_ = lean_unsigned_to_nat(1);
                                        v_id_3842_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3841_);
                                        v___x_3843_ = lean_unsigned_to_nat(3);
                                        v___x_3844_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3843_);
                                        lean_dec(v_x_3741_);
                                        v___x_3845_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                        lean_inc(v___x_3844_);
                                        v___x_3846_ =
                                            l_Lean_Syntax_isOfKind(v___x_3844_, v___x_3845_);
                                        if v___x_3846_ == 0 {
                                            v_quotContext_3847_ = lean_ctor_get(v_a_3742_, 1);
                                            v_currMacroScope_3848_ = lean_ctor_get(v_a_3742_, 2);
                                            v_ref_3849_ = lean_ctor_get(v_a_3742_, 5);
                                            v___x_3850_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_3849_, v___x_3846_);
                                            v___x_3851_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                            v___x_3852_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
                                            v___x_3853_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
                                            lean_inc(v_currMacroScope_3848_);
                                            lean_inc(v_quotContext_3847_);
                                            v___x_3854_ = l_Lean_addMacroScope(
                                                v_quotContext_3847_,
                                                v___x_3853_,
                                                v_currMacroScope_3848_,
                                            );
                                            v___x_3855_ = lean_box(0);
                                            v___x_3856_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
                                            lean_inc(v___x_3850_);
                                            v___x_3857_ = lean_alloc_ctor(3, 4, (0) as u32);
                                            lean_ctor_set(v___x_3857_, 0, v___x_3850_);
                                            lean_ctor_set(v___x_3857_, 1, v___x_3852_);
                                            lean_ctor_set(v___x_3857_, 2, v___x_3854_);
                                            lean_ctor_set(v___x_3857_, 3, v___x_3856_);
                                            v___x_3858_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                            v___x_3864_ = l_Lean_TSyntax_getId(v_id_3842_);
                                            lean_dec(v_id_3842_);
                                            lean_inc(v___x_3864_);
                                            v___x_3865_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3855_, v___x_3864_);
                                            if lean_obj_tag(v___x_3865_) == 0 {
                                                v___x_3866_ = l_Lean_quoteNameMk(v___x_3864_);
                                                v___y_3860_ = v___x_3866_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_dec(v___x_3864_);
                                                v_val_3867_ = lean_ctor_get(v___x_3865_, 0);
                                                lean_inc(v_val_3867_);
                                                lean_dec_ref_known(v___x_3865_, 1);
                                                v___x_3868_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                                v___x_3869_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                                v___x_3870_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                                v___x_3871_ = lean_string_intercalate(
                                                    v___x_3870_,
                                                    v_val_3867_,
                                                );
                                                v___x_3872_ =
                                                    lean_string_append(v___x_3869_, v___x_3871_);
                                                lean_dec_ref(v___x_3871_);
                                                v___x_3873_ = lean_box(2);
                                                v___x_3874_ = l_Lean_Syntax_mkNameLit(
                                                    v___x_3872_,
                                                    v___x_3873_,
                                                );
                                                v___x_3875_ =
                                                    lean_mk_empty_array_with_capacity(v___x_3841_);
                                                v___x_3876_ =
                                                    lean_array_push(v___x_3875_, v___x_3874_);
                                                v___x_3877_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                lean_ctor_set(v___x_3877_, 0, v___x_3873_);
                                                lean_ctor_set(v___x_3877_, 1, v___x_3868_);
                                                lean_ctor_set(v___x_3877_, 2, v___x_3876_);
                                                v___y_3860_ = v___x_3877_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            v_quotContext_3878_ = lean_ctor_get(v_a_3742_, 1);
                                            v_currMacroScope_3879_ = lean_ctor_get(v_a_3742_, 2);
                                            v_ref_3880_ = lean_ctor_get(v_a_3742_, 5);
                                            v___x_3881_ =
                                                l_Lean_SourceInfo_fromRef(v_ref_3880_, v___x_3751_);
                                            v___x_3882_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                            v___x_3883_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__34);
                                            v___x_3884_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__36;
                                            lean_inc(v_currMacroScope_3879_);
                                            lean_inc(v_quotContext_3878_);
                                            v___x_3885_ = l_Lean_addMacroScope(
                                                v_quotContext_3878_,
                                                v___x_3884_,
                                                v_currMacroScope_3879_,
                                            );
                                            v___x_3886_ = lean_box(0);
                                            v___x_3887_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__38;
                                            lean_inc(v___x_3881_);
                                            v___x_3888_ = lean_alloc_ctor(3, 4, (0) as u32);
                                            lean_ctor_set(v___x_3888_, 0, v___x_3881_);
                                            lean_ctor_set(v___x_3888_, 1, v___x_3883_);
                                            lean_ctor_set(v___x_3888_, 2, v___x_3885_);
                                            lean_ctor_set(v___x_3888_, 3, v___x_3887_);
                                            v___x_3889_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                            v___x_3899_ = l_Lean_TSyntax_getId(v_id_3842_);
                                            lean_dec(v_id_3842_);
                                            lean_inc(v___x_3899_);
                                            v___x_3900_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3886_, v___x_3899_);
                                            if lean_obj_tag(v___x_3900_) == 0 {
                                                v___x_3901_ = l_Lean_quoteNameMk(v___x_3899_);
                                                v___y_3891_ = v___x_3901_;
                                                state = 4;
                                                continue;
                                            } else {
                                                lean_dec(v___x_3899_);
                                                v_val_3902_ = lean_ctor_get(v___x_3900_, 0);
                                                lean_inc(v_val_3902_);
                                                lean_dec_ref_known(v___x_3900_, 1);
                                                v___x_3903_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                                v___x_3904_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                                v___x_3905_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                                v___x_3906_ = lean_string_intercalate(
                                                    v___x_3905_,
                                                    v_val_3902_,
                                                );
                                                v___x_3907_ =
                                                    lean_string_append(v___x_3904_, v___x_3906_);
                                                lean_dec_ref(v___x_3906_);
                                                v___x_3908_ = lean_box(2);
                                                v___x_3909_ = l_Lean_Syntax_mkNameLit(
                                                    v___x_3907_,
                                                    v___x_3908_,
                                                );
                                                v___x_3910_ =
                                                    lean_mk_empty_array_with_capacity(v___x_3841_);
                                                v___x_3911_ =
                                                    lean_array_push(v___x_3910_, v___x_3909_);
                                                v___x_3912_ = lean_alloc_ctor(1, 3, (0) as u32);
                                                lean_ctor_set(v___x_3912_, 0, v___x_3908_);
                                                lean_ctor_set(v___x_3912_, 1, v___x_3903_);
                                                lean_ctor_set(v___x_3912_, 2, v___x_3911_);
                                                v___y_3891_ = v___x_3912_;
                                                state = 4;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                v___x_3913_ = lean_unsigned_to_nat(0);
                                v___x_3914_ = lean_unsigned_to_nat(3);
                                v___x_3915_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3914_);
                                v___x_3916_ = l_Lean_Syntax_matchesNull(v___x_3915_, v___x_3913_);
                                if v___x_3916_ == 0 {
                                    lean_dec(v_x_3741_);
                                    v___x_3917_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                    return v___x_3917_;
                                } else {
                                    v___x_3918_ = lean_unsigned_to_nat(1);
                                    v___x_3919_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3918_);
                                    v___x_3920_ = lean_unsigned_to_nat(2);
                                    v_id_3921_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3920_);
                                    v___x_3922_ = lean_unsigned_to_nat(4);
                                    v___x_3923_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3922_);
                                    lean_dec(v_x_3741_);
                                    v___x_3924_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                    lean_inc(v___x_3923_);
                                    v___x_3925_ = l_Lean_Syntax_isOfKind(v___x_3923_, v___x_3924_);
                                    if v___x_3925_ == 0 {
                                        v_quotContext_3926_ = lean_ctor_get(v_a_3742_, 1);
                                        v_currMacroScope_3927_ = lean_ctor_get(v_a_3742_, 2);
                                        v_ref_3928_ = lean_ctor_get(v_a_3742_, 5);
                                        v___x_3929_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_3928_, v___x_3925_);
                                        v___x_3930_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                        v___x_3931_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
                                        v___x_3932_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
                                        lean_inc(v_currMacroScope_3927_);
                                        lean_inc(v_quotContext_3926_);
                                        v___x_3933_ = l_Lean_addMacroScope(
                                            v_quotContext_3926_,
                                            v___x_3932_,
                                            v_currMacroScope_3927_,
                                        );
                                        v___x_3934_ = lean_box(0);
                                        v___x_3935_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
                                        lean_inc(v___x_3929_);
                                        v___x_3936_ = lean_alloc_ctor(3, 4, (0) as u32);
                                        lean_ctor_set(v___x_3936_, 0, v___x_3929_);
                                        lean_ctor_set(v___x_3936_, 1, v___x_3931_);
                                        lean_ctor_set(v___x_3936_, 2, v___x_3933_);
                                        lean_ctor_set(v___x_3936_, 3, v___x_3935_);
                                        v___x_3937_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                        v___x_3943_ = l_Lean_TSyntax_getId(v_id_3921_);
                                        lean_dec(v_id_3921_);
                                        lean_inc(v___x_3943_);
                                        v___x_3944_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3934_, v___x_3943_);
                                        if lean_obj_tag(v___x_3944_) == 0 {
                                            v___x_3945_ = l_Lean_quoteNameMk(v___x_3943_);
                                            v___y_3939_ = v___x_3945_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_dec(v___x_3943_);
                                            v_val_3946_ = lean_ctor_get(v___x_3944_, 0);
                                            lean_inc(v_val_3946_);
                                            lean_dec_ref_known(v___x_3944_, 1);
                                            v___x_3947_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                            v___x_3948_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                            v___x_3949_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                            v___x_3950_ =
                                                lean_string_intercalate(v___x_3949_, v_val_3946_);
                                            v___x_3951_ =
                                                lean_string_append(v___x_3948_, v___x_3950_);
                                            lean_dec_ref(v___x_3950_);
                                            v___x_3952_ = lean_box(2);
                                            v___x_3953_ =
                                                l_Lean_Syntax_mkNameLit(v___x_3951_, v___x_3952_);
                                            v___x_3954_ =
                                                lean_mk_empty_array_with_capacity(v___x_3918_);
                                            v___x_3955_ = lean_array_push(v___x_3954_, v___x_3953_);
                                            v___x_3956_ = lean_alloc_ctor(1, 3, (0) as u32);
                                            lean_ctor_set(v___x_3956_, 0, v___x_3952_);
                                            lean_ctor_set(v___x_3956_, 1, v___x_3947_);
                                            lean_ctor_set(v___x_3956_, 2, v___x_3955_);
                                            v___y_3939_ = v___x_3956_;
                                            state = 5;
                                            continue;
                                        }
                                    } else {
                                        v_quotContext_3957_ = lean_ctor_get(v_a_3742_, 1);
                                        v_currMacroScope_3958_ = lean_ctor_get(v_a_3742_, 2);
                                        v_ref_3959_ = lean_ctor_get(v_a_3742_, 5);
                                        v___x_3960_ =
                                            l_Lean_SourceInfo_fromRef(v_ref_3959_, v___x_3749_);
                                        v___x_3961_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                        v___x_3962_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__40);
                                        v___x_3963_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__42;
                                        lean_inc(v_currMacroScope_3958_);
                                        lean_inc(v_quotContext_3957_);
                                        v___x_3964_ = l_Lean_addMacroScope(
                                            v_quotContext_3957_,
                                            v___x_3963_,
                                            v_currMacroScope_3958_,
                                        );
                                        v___x_3965_ = lean_box(0);
                                        v___x_3966_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__44;
                                        lean_inc(v___x_3960_);
                                        v___x_3967_ = lean_alloc_ctor(3, 4, (0) as u32);
                                        lean_ctor_set(v___x_3967_, 0, v___x_3960_);
                                        lean_ctor_set(v___x_3967_, 1, v___x_3962_);
                                        lean_ctor_set(v___x_3967_, 2, v___x_3964_);
                                        lean_ctor_set(v___x_3967_, 3, v___x_3966_);
                                        v___x_3968_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                        v___x_3978_ = l_Lean_TSyntax_getId(v_id_3921_);
                                        lean_dec(v_id_3921_);
                                        lean_inc(v___x_3978_);
                                        v___x_3979_ = l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(v___x_3965_, v___x_3978_);
                                        if lean_obj_tag(v___x_3979_) == 0 {
                                            v___x_3980_ = l_Lean_quoteNameMk(v___x_3978_);
                                            v___y_3970_ = v___x_3980_;
                                            state = 6;
                                            continue;
                                        } else {
                                            lean_dec(v___x_3978_);
                                            v_val_3981_ = lean_ctor_get(v___x_3979_, 0);
                                            lean_inc(v_val_3981_);
                                            lean_dec_ref_known(v___x_3979_, 1);
                                            v___x_3982_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                            v___x_3983_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                            v___x_3984_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                            v___x_3985_ =
                                                lean_string_intercalate(v___x_3984_, v_val_3981_);
                                            v___x_3986_ =
                                                lean_string_append(v___x_3983_, v___x_3985_);
                                            lean_dec_ref(v___x_3985_);
                                            v___x_3987_ = lean_box(2);
                                            v___x_3988_ =
                                                l_Lean_Syntax_mkNameLit(v___x_3986_, v___x_3987_);
                                            v___x_3989_ =
                                                lean_mk_empty_array_with_capacity(v___x_3918_);
                                            v___x_3990_ = lean_array_push(v___x_3989_, v___x_3988_);
                                            v___x_3991_ = lean_alloc_ctor(1, 3, (0) as u32);
                                            lean_ctor_set(v___x_3991_, 0, v___x_3987_);
                                            lean_ctor_set(v___x_3991_, 1, v___x_3982_);
                                            lean_ctor_set(v___x_3991_, 2, v___x_3990_);
                                            v___y_3970_ = v___x_3991_;
                                            state = 6;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            v___x_3992_ = lean_unsigned_to_nat(0);
                            v___x_3993_ = lean_unsigned_to_nat(2);
                            v___x_3994_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3993_);
                            v___x_3995_ = l_Lean_Syntax_matchesNull(v___x_3994_, v___x_3992_);
                            if v___x_3995_ == 0 {
                                lean_dec(v_x_3741_);
                                v___x_3996_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                                return v___x_3996_;
                            } else {
                                v___x_3997_ = lean_unsigned_to_nat(1);
                                v_id_3998_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3997_);
                                v___x_3999_ = lean_unsigned_to_nat(3);
                                v___x_4000_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_3999_);
                                lean_dec(v_x_3741_);
                                v___x_4001_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                                lean_inc(v___x_4000_);
                                v___x_4002_ = l_Lean_Syntax_isOfKind(v___x_4000_, v___x_4001_);
                                if v___x_4002_ == 0 {
                                    v_quotContext_4003_ = lean_ctor_get(v_a_3742_, 1);
                                    v_currMacroScope_4004_ = lean_ctor_get(v_a_3742_, 2);
                                    v_ref_4005_ = lean_ctor_get(v_a_3742_, 5);
                                    v___x_4006_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4005_, v___x_4002_);
                                    v___x_4007_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                    v___x_4008_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
                                    v___x_4009_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
                                    lean_inc(v_currMacroScope_4004_);
                                    lean_inc(v_quotContext_4003_);
                                    v___x_4010_ = l_Lean_addMacroScope(
                                        v_quotContext_4003_,
                                        v___x_4009_,
                                        v_currMacroScope_4004_,
                                    );
                                    v___x_4011_ = lean_box(0);
                                    v___x_4012_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
                                    lean_inc(v___x_4006_);
                                    v___x_4013_ = lean_alloc_ctor(3, 4, (0) as u32);
                                    lean_ctor_set(v___x_4013_, 0, v___x_4006_);
                                    lean_ctor_set(v___x_4013_, 1, v___x_4008_);
                                    lean_ctor_set(v___x_4013_, 2, v___x_4010_);
                                    lean_ctor_set(v___x_4013_, 3, v___x_4012_);
                                    v___x_4014_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                    v___x_4020_ = l_Lean_TSyntax_getId(v_id_3998_);
                                    lean_dec(v_id_3998_);
                                    lean_inc(v___x_4020_);
                                    v___x_4021_ =
                                        l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                            v___x_4011_,
                                            v___x_4020_,
                                        );
                                    if lean_obj_tag(v___x_4021_) == 0 {
                                        v___x_4022_ = l_Lean_quoteNameMk(v___x_4020_);
                                        v___y_4016_ = v___x_4022_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_dec(v___x_4020_);
                                        v_val_4023_ = lean_ctor_get(v___x_4021_, 0);
                                        lean_inc(v_val_4023_);
                                        lean_dec_ref_known(v___x_4021_, 1);
                                        v___x_4024_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                        v___x_4025_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                        v___x_4026_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                        v___x_4027_ =
                                            lean_string_intercalate(v___x_4026_, v_val_4023_);
                                        v___x_4028_ = lean_string_append(v___x_4025_, v___x_4027_);
                                        lean_dec_ref(v___x_4027_);
                                        v___x_4029_ = lean_box(2);
                                        v___x_4030_ =
                                            l_Lean_Syntax_mkNameLit(v___x_4028_, v___x_4029_);
                                        v___x_4031_ =
                                            lean_mk_empty_array_with_capacity(v___x_3997_);
                                        v___x_4032_ = lean_array_push(v___x_4031_, v___x_4030_);
                                        v___x_4033_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_4033_, 0, v___x_4029_);
                                        lean_ctor_set(v___x_4033_, 1, v___x_4024_);
                                        lean_ctor_set(v___x_4033_, 2, v___x_4032_);
                                        v___y_4016_ = v___x_4033_;
                                        state = 7;
                                        continue;
                                    }
                                } else {
                                    v_quotContext_4034_ = lean_ctor_get(v_a_3742_, 1);
                                    v_currMacroScope_4035_ = lean_ctor_get(v_a_3742_, 2);
                                    v_ref_4036_ = lean_ctor_get(v_a_3742_, 5);
                                    v___x_4037_ =
                                        l_Lean_SourceInfo_fromRef(v_ref_4036_, v___x_3747_);
                                    v___x_4038_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                    v___x_4039_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__46);
                                    v___x_4040_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__48;
                                    lean_inc(v_currMacroScope_4035_);
                                    lean_inc(v_quotContext_4034_);
                                    v___x_4041_ = l_Lean_addMacroScope(
                                        v_quotContext_4034_,
                                        v___x_4040_,
                                        v_currMacroScope_4035_,
                                    );
                                    v___x_4042_ = lean_box(0);
                                    v___x_4043_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__50;
                                    lean_inc(v___x_4037_);
                                    v___x_4044_ = lean_alloc_ctor(3, 4, (0) as u32);
                                    lean_ctor_set(v___x_4044_, 0, v___x_4037_);
                                    lean_ctor_set(v___x_4044_, 1, v___x_4039_);
                                    lean_ctor_set(v___x_4044_, 2, v___x_4041_);
                                    lean_ctor_set(v___x_4044_, 3, v___x_4043_);
                                    v___x_4045_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                    v___x_4055_ = l_Lean_TSyntax_getId(v_id_3998_);
                                    lean_dec(v_id_3998_);
                                    lean_inc(v___x_4055_);
                                    v___x_4056_ =
                                        l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                            v___x_4042_,
                                            v___x_4055_,
                                        );
                                    if lean_obj_tag(v___x_4056_) == 0 {
                                        v___x_4057_ = l_Lean_quoteNameMk(v___x_4055_);
                                        v___y_4047_ = v___x_4057_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_dec(v___x_4055_);
                                        v_val_4058_ = lean_ctor_get(v___x_4056_, 0);
                                        lean_inc(v_val_4058_);
                                        lean_dec_ref_known(v___x_4056_, 1);
                                        v___x_4059_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                        v___x_4060_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                        v___x_4061_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                        v___x_4062_ =
                                            lean_string_intercalate(v___x_4061_, v_val_4058_);
                                        v___x_4063_ = lean_string_append(v___x_4060_, v___x_4062_);
                                        lean_dec_ref(v___x_4062_);
                                        v___x_4064_ = lean_box(2);
                                        v___x_4065_ =
                                            l_Lean_Syntax_mkNameLit(v___x_4063_, v___x_4064_);
                                        v___x_4066_ =
                                            lean_mk_empty_array_with_capacity(v___x_3997_);
                                        v___x_4067_ = lean_array_push(v___x_4066_, v___x_4065_);
                                        v___x_4068_ = lean_alloc_ctor(1, 3, (0) as u32);
                                        lean_ctor_set(v___x_4068_, 0, v___x_4064_);
                                        lean_ctor_set(v___x_4068_, 1, v___x_4059_);
                                        lean_ctor_set(v___x_4068_, 2, v___x_4067_);
                                        v___y_4047_ = v___x_4068_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_4069_ = lean_unsigned_to_nat(0);
                        v___x_4070_ = lean_unsigned_to_nat(3);
                        v___x_4071_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4070_);
                        v___x_4072_ = l_Lean_Syntax_matchesNull(v___x_4071_, v___x_4069_);
                        if v___x_4072_ == 0 {
                            lean_dec(v_x_3741_);
                            v___x_4073_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                            return v___x_4073_;
                        } else {
                            v___x_4074_ = lean_unsigned_to_nat(1);
                            v___x_4075_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4074_);
                            v___x_4076_ = lean_unsigned_to_nat(2);
                            v_id_4077_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4076_);
                            v___x_4078_ = lean_unsigned_to_nat(4);
                            v___x_4079_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4078_);
                            lean_dec(v_x_3741_);
                            v___x_4080_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                            lean_inc(v___x_4079_);
                            v___x_4081_ = l_Lean_Syntax_isOfKind(v___x_4079_, v___x_4080_);
                            if v___x_4081_ == 0 {
                                v_quotContext_4082_ = lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4083_ = lean_ctor_get(v_a_3742_, 2);
                                v_ref_4084_ = lean_ctor_get(v_a_3742_, 5);
                                v___x_4085_ = l_Lean_SourceInfo_fromRef(v_ref_4084_, v___x_4081_);
                                v___x_4086_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4087_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
                                v___x_4088_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
                                lean_inc(v_currMacroScope_4083_);
                                lean_inc(v_quotContext_4082_);
                                v___x_4089_ = l_Lean_addMacroScope(
                                    v_quotContext_4082_,
                                    v___x_4088_,
                                    v_currMacroScope_4083_,
                                );
                                v___x_4090_ = lean_box(0);
                                v___x_4091_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
                                lean_inc(v___x_4085_);
                                v___x_4092_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_4092_, 0, v___x_4085_);
                                lean_ctor_set(v___x_4092_, 1, v___x_4087_);
                                lean_ctor_set(v___x_4092_, 2, v___x_4089_);
                                lean_ctor_set(v___x_4092_, 3, v___x_4091_);
                                v___x_4093_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4099_ = l_Lean_TSyntax_getId(v_id_4077_);
                                lean_dec(v_id_4077_);
                                lean_inc(v___x_4099_);
                                v___x_4100_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4090_,
                                        v___x_4099_,
                                    );
                                if lean_obj_tag(v___x_4100_) == 0 {
                                    v___x_4101_ = l_Lean_quoteNameMk(v___x_4099_);
                                    v___y_4095_ = v___x_4101_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_dec(v___x_4099_);
                                    v_val_4102_ = lean_ctor_get(v___x_4100_, 0);
                                    lean_inc(v_val_4102_);
                                    lean_dec_ref_known(v___x_4100_, 1);
                                    v___x_4103_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4104_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4105_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4106_ = lean_string_intercalate(v___x_4105_, v_val_4102_);
                                    v___x_4107_ = lean_string_append(v___x_4104_, v___x_4106_);
                                    lean_dec_ref(v___x_4106_);
                                    v___x_4108_ = lean_box(2);
                                    v___x_4109_ = l_Lean_Syntax_mkNameLit(v___x_4107_, v___x_4108_);
                                    v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4074_);
                                    v___x_4111_ = lean_array_push(v___x_4110_, v___x_4109_);
                                    v___x_4112_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_4112_, 0, v___x_4108_);
                                    lean_ctor_set(v___x_4112_, 1, v___x_4103_);
                                    lean_ctor_set(v___x_4112_, 2, v___x_4111_);
                                    v___y_4095_ = v___x_4112_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v_quotContext_4113_ = lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4114_ = lean_ctor_get(v_a_3742_, 2);
                                v_ref_4115_ = lean_ctor_get(v_a_3742_, 5);
                                v___x_4116_ = l_Lean_SourceInfo_fromRef(v_ref_4115_, v___x_3745_);
                                v___x_4117_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4118_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__52);
                                v___x_4119_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__54;
                                lean_inc(v_currMacroScope_4114_);
                                lean_inc(v_quotContext_4113_);
                                v___x_4120_ = l_Lean_addMacroScope(
                                    v_quotContext_4113_,
                                    v___x_4119_,
                                    v_currMacroScope_4114_,
                                );
                                v___x_4121_ = lean_box(0);
                                v___x_4122_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__56;
                                lean_inc(v___x_4116_);
                                v___x_4123_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_4123_, 0, v___x_4116_);
                                lean_ctor_set(v___x_4123_, 1, v___x_4118_);
                                lean_ctor_set(v___x_4123_, 2, v___x_4120_);
                                lean_ctor_set(v___x_4123_, 3, v___x_4122_);
                                v___x_4124_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4134_ = l_Lean_TSyntax_getId(v_id_4077_);
                                lean_dec(v_id_4077_);
                                lean_inc(v___x_4134_);
                                v___x_4135_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4121_,
                                        v___x_4134_,
                                    );
                                if lean_obj_tag(v___x_4135_) == 0 {
                                    v___x_4136_ = l_Lean_quoteNameMk(v___x_4134_);
                                    v___y_4126_ = v___x_4136_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_dec(v___x_4134_);
                                    v_val_4137_ = lean_ctor_get(v___x_4135_, 0);
                                    lean_inc(v_val_4137_);
                                    lean_dec_ref_known(v___x_4135_, 1);
                                    v___x_4138_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4139_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4140_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4141_ = lean_string_intercalate(v___x_4140_, v_val_4137_);
                                    v___x_4142_ = lean_string_append(v___x_4139_, v___x_4141_);
                                    lean_dec_ref(v___x_4141_);
                                    v___x_4143_ = lean_box(2);
                                    v___x_4144_ = l_Lean_Syntax_mkNameLit(v___x_4142_, v___x_4143_);
                                    v___x_4145_ = lean_mk_empty_array_with_capacity(v___x_4074_);
                                    v___x_4146_ = lean_array_push(v___x_4145_, v___x_4144_);
                                    v___x_4147_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_4147_, 0, v___x_4143_);
                                    lean_ctor_set(v___x_4147_, 1, v___x_4138_);
                                    lean_ctor_set(v___x_4147_, 2, v___x_4146_);
                                    v___y_4126_ = v___x_4147_;
                                    state = 10;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    v___x_4148_ = lean_unsigned_to_nat(0);
                    v___x_4149_ = lean_unsigned_to_nat(1);
                    v_id_4150_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4149_);
                    v___x_4151_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
                    lean_inc(v_id_4150_);
                    v___x_4152_ = l_Lean_Syntax_isOfKind(v_id_4150_, v___x_4151_);
                    if v___x_4152_ == 0 {
                        v___x_4153_ = lean_unsigned_to_nat(2);
                        v___x_4154_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4153_);
                        v___x_4155_ = l_Lean_Syntax_matchesNull(v___x_4154_, v___x_4148_);
                        if v___x_4155_ == 0 {
                            lean_dec(v_id_4150_);
                            lean_dec(v_x_3741_);
                            v___x_4156_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                            return v___x_4156_;
                        } else {
                            v_quotContext_4157_ = lean_ctor_get(v_a_3742_, 1);
                            v_currMacroScope_4158_ = lean_ctor_get(v_a_3742_, 2);
                            v_ref_4159_ = lean_ctor_get(v_a_3742_, 5);
                            v___x_4160_ = lean_unsigned_to_nat(3);
                            v___x_4161_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4160_);
                            lean_dec(v_x_3741_);
                            v___x_4162_ = l_Lean_SourceInfo_fromRef(v_ref_4159_, v___x_4152_);
                            v___x_4163_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                            v___x_4164_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
                            v___x_4165_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
                            lean_inc(v_currMacroScope_4158_);
                            lean_inc(v_quotContext_4157_);
                            v___x_4166_ = l_Lean_addMacroScope(
                                v_quotContext_4157_,
                                v___x_4165_,
                                v_currMacroScope_4158_,
                            );
                            v___x_4167_ = lean_box(0);
                            v___x_4168_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
                            lean_inc(v___x_4162_);
                            v___x_4169_ = lean_alloc_ctor(3, 4, (0) as u32);
                            lean_ctor_set(v___x_4169_, 0, v___x_4162_);
                            lean_ctor_set(v___x_4169_, 1, v___x_4164_);
                            lean_ctor_set(v___x_4169_, 2, v___x_4166_);
                            lean_ctor_set(v___x_4169_, 3, v___x_4168_);
                            v___x_4170_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                            v___x_4176_ = l_Lean_TSyntax_getId(v_id_4150_);
                            lean_dec(v_id_4150_);
                            lean_inc(v___x_4176_);
                            v___x_4177_ =
                                l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                    v___x_4167_,
                                    v___x_4176_,
                                );
                            if lean_obj_tag(v___x_4177_) == 0 {
                                v___x_4178_ = l_Lean_quoteNameMk(v___x_4176_);
                                v___y_4172_ = v___x_4178_;
                                state = 11;
                                continue;
                            } else {
                                lean_dec(v___x_4176_);
                                v_val_4179_ = lean_ctor_get(v___x_4177_, 0);
                                lean_inc(v_val_4179_);
                                lean_dec_ref_known(v___x_4177_, 1);
                                v___x_4180_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                v___x_4181_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                v___x_4182_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                v___x_4183_ = lean_string_intercalate(v___x_4182_, v_val_4179_);
                                v___x_4184_ = lean_string_append(v___x_4181_, v___x_4183_);
                                lean_dec_ref(v___x_4183_);
                                v___x_4185_ = lean_box(2);
                                v___x_4186_ = l_Lean_Syntax_mkNameLit(v___x_4184_, v___x_4185_);
                                v___x_4187_ = lean_mk_empty_array_with_capacity(v___x_4149_);
                                v___x_4188_ = lean_array_push(v___x_4187_, v___x_4186_);
                                v___x_4189_ = lean_alloc_ctor(1, 3, (0) as u32);
                                lean_ctor_set(v___x_4189_, 0, v___x_4185_);
                                lean_ctor_set(v___x_4189_, 1, v___x_4180_);
                                lean_ctor_set(v___x_4189_, 2, v___x_4188_);
                                v___y_4172_ = v___x_4189_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        v___x_4190_ = lean_unsigned_to_nat(2);
                        v___x_4191_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4190_);
                        v___x_4192_ = l_Lean_Syntax_matchesNull(v___x_4191_, v___x_4148_);
                        if v___x_4192_ == 0 {
                            lean_dec(v_id_4150_);
                            lean_dec(v_x_3741_);
                            v___x_4193_ = l_Lean_Macro_throwUnsupported___redArg(v_a_3743_);
                            return v___x_4193_;
                        } else {
                            v___x_4194_ = lean_unsigned_to_nat(3);
                            v___x_4195_ = l_Lean_Syntax_getArg(v_x_3741_, v___x_4194_);
                            lean_dec(v_x_3741_);
                            v___x_4196_ =
                                l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__15;
                            lean_inc(v___x_4195_);
                            v___x_4197_ = l_Lean_Syntax_isOfKind(v___x_4195_, v___x_4196_);
                            if v___x_4197_ == 0 {
                                v_quotContext_4198_ = lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4199_ = lean_ctor_get(v_a_3742_, 2);
                                v_ref_4200_ = lean_ctor_get(v_a_3742_, 5);
                                v___x_4201_ = l_Lean_SourceInfo_fromRef(v_ref_4200_, v___x_4197_);
                                v___x_4202_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4203_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
                                v___x_4204_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
                                lean_inc(v_currMacroScope_4199_);
                                lean_inc(v_quotContext_4198_);
                                v___x_4205_ = l_Lean_addMacroScope(
                                    v_quotContext_4198_,
                                    v___x_4204_,
                                    v_currMacroScope_4199_,
                                );
                                v___x_4206_ = lean_box(0);
                                v___x_4207_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
                                lean_inc(v___x_4201_);
                                v___x_4208_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_4208_, 0, v___x_4201_);
                                lean_ctor_set(v___x_4208_, 1, v___x_4203_);
                                lean_ctor_set(v___x_4208_, 2, v___x_4205_);
                                lean_ctor_set(v___x_4208_, 3, v___x_4207_);
                                v___x_4209_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4215_ = l_Lean_TSyntax_getId(v_id_4150_);
                                lean_dec(v_id_4150_);
                                lean_inc(v___x_4215_);
                                v___x_4216_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4206_,
                                        v___x_4215_,
                                    );
                                if lean_obj_tag(v___x_4216_) == 0 {
                                    v___x_4217_ = l_Lean_quoteNameMk(v___x_4215_);
                                    v___y_4211_ = v___x_4217_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_dec(v___x_4215_);
                                    v_val_4218_ = lean_ctor_get(v___x_4216_, 0);
                                    lean_inc(v_val_4218_);
                                    lean_dec_ref_known(v___x_4216_, 1);
                                    v___x_4219_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4220_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4221_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4222_ = lean_string_intercalate(v___x_4221_, v_val_4218_);
                                    v___x_4223_ = lean_string_append(v___x_4220_, v___x_4222_);
                                    lean_dec_ref(v___x_4222_);
                                    v___x_4224_ = lean_box(2);
                                    v___x_4225_ = l_Lean_Syntax_mkNameLit(v___x_4223_, v___x_4224_);
                                    v___x_4226_ = lean_mk_empty_array_with_capacity(v___x_4149_);
                                    v___x_4227_ = lean_array_push(v___x_4226_, v___x_4225_);
                                    v___x_4228_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_4228_, 0, v___x_4224_);
                                    lean_ctor_set(v___x_4228_, 1, v___x_4219_);
                                    lean_ctor_set(v___x_4228_, 2, v___x_4227_);
                                    v___y_4211_ = v___x_4228_;
                                    state = 12;
                                    continue;
                                }
                            } else {
                                v_quotContext_4229_ = lean_ctor_get(v_a_3742_, 1);
                                v_currMacroScope_4230_ = lean_ctor_get(v_a_3742_, 2);
                                v_ref_4231_ = lean_ctor_get(v_a_3742_, 5);
                                v___x_4232_ = 0;
                                v___x_4233_ = l_Lean_SourceInfo_fromRef(v_ref_4231_, v___x_4232_);
                                v___x_4234_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__17;
                                v___x_4235_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60_once), _init_l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__60);
                                v___x_4236_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__62;
                                lean_inc(v_currMacroScope_4230_);
                                lean_inc(v_quotContext_4229_);
                                v___x_4237_ = l_Lean_addMacroScope(
                                    v_quotContext_4229_,
                                    v___x_4236_,
                                    v_currMacroScope_4230_,
                                );
                                v___x_4238_ = lean_box(0);
                                v___x_4239_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__64;
                                lean_inc(v___x_4233_);
                                v___x_4240_ = lean_alloc_ctor(3, 4, (0) as u32);
                                lean_ctor_set(v___x_4240_, 0, v___x_4233_);
                                lean_ctor_set(v___x_4240_, 1, v___x_4235_);
                                lean_ctor_set(v___x_4240_, 2, v___x_4237_);
                                lean_ctor_set(v___x_4240_, 3, v___x_4239_);
                                v___x_4241_ =
                                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__25;
                                v___x_4251_ = l_Lean_TSyntax_getId(v_id_4150_);
                                lean_dec(v_id_4150_);
                                lean_inc(v___x_4251_);
                                v___x_4252_ =
                                    l___private_Init_Meta_Defs_0__Lean_getEscapedNameParts_x3f(
                                        v___x_4238_,
                                        v___x_4251_,
                                    );
                                if lean_obj_tag(v___x_4252_) == 0 {
                                    v___x_4253_ = l_Lean_quoteNameMk(v___x_4251_);
                                    v___y_4243_ = v___x_4253_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_dec(v___x_4251_);
                                    v_val_4254_ = lean_ctor_get(v___x_4252_, 0);
                                    lean_inc(v_val_4254_);
                                    lean_dec_ref_known(v___x_4252_, 1);
                                    v___x_4255_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__27;
                                    v___x_4256_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
                                    v___x_4257_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__29;
                                    v___x_4258_ = lean_string_intercalate(v___x_4257_, v_val_4254_);
                                    v___x_4259_ = lean_string_append(v___x_4256_, v___x_4258_);
                                    lean_dec_ref(v___x_4258_);
                                    v___x_4260_ = lean_box(2);
                                    v___x_4261_ = l_Lean_Syntax_mkNameLit(v___x_4259_, v___x_4260_);
                                    v___x_4262_ = lean_mk_empty_array_with_capacity(v___x_4149_);
                                    v___x_4263_ = lean_array_push(v___x_4262_, v___x_4261_);
                                    v___x_4264_ = lean_alloc_ctor(1, 3, (0) as u32);
                                    lean_ctor_set(v___x_4264_, 0, v___x_4260_);
                                    lean_ctor_set(v___x_4264_, 1, v___x_4255_);
                                    lean_ctor_set(v___x_4264_, 2, v___x_4263_);
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
                lean_inc(v___x_3773_);
                v___x_3784_ = l_Lean_Syntax_node3(
                    v___x_3773_,
                    v___x_3781_,
                    v___x_3763_,
                    v___y_3783_,
                    v___x_3767_,
                );
                v___x_3785_ =
                    l_Lean_Syntax_node2(v___x_3773_, v___x_3774_, v___x_3780_, v___x_3784_);
                v___x_3786_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3786_, 0, v___x_3785_);
                lean_ctor_set(v___x_3786_, 1, v_a_3743_);
                return v___x_3786_;
            }
            2 => {
                v___x_3815_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_3816_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                lean_inc_n(v___x_3804_, 3);
                v___x_3817_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3817_, 0, v___x_3804_);
                lean_ctor_set(v___x_3817_, 1, v___x_3816_);
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
                v___x_3821_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3821_, 0, v___x_3820_);
                lean_ctor_set(v___x_3821_, 1, v_a_3743_);
                return v___x_3821_;
            }
            3 => {
                lean_inc(v___x_3850_);
                v___x_3861_ =
                    l_Lean_Syntax_node2(v___x_3850_, v___x_3858_, v___y_3860_, v___x_3844_);
                v___x_3862_ =
                    l_Lean_Syntax_node2(v___x_3850_, v___x_3851_, v___x_3857_, v___x_3861_);
                v___x_3863_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3863_, 0, v___x_3862_);
                lean_ctor_set(v___x_3863_, 1, v_a_3743_);
                return v___x_3863_;
            }
            4 => {
                v___x_3892_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_3893_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                lean_inc_n(v___x_3881_, 3);
                v___x_3894_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3894_, 0, v___x_3881_);
                lean_ctor_set(v___x_3894_, 1, v___x_3893_);
                v___x_3895_ =
                    l_Lean_Syntax_node2(v___x_3881_, v___x_3892_, v___x_3894_, v___x_3844_);
                v___x_3896_ =
                    l_Lean_Syntax_node2(v___x_3881_, v___x_3889_, v___y_3891_, v___x_3895_);
                v___x_3897_ =
                    l_Lean_Syntax_node2(v___x_3881_, v___x_3882_, v___x_3888_, v___x_3896_);
                v___x_3898_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                lean_ctor_set(v___x_3898_, 1, v_a_3743_);
                return v___x_3898_;
            }
            5 => {
                lean_inc(v___x_3929_);
                v___x_3940_ = l_Lean_Syntax_node3(
                    v___x_3929_,
                    v___x_3937_,
                    v___x_3919_,
                    v___y_3939_,
                    v___x_3923_,
                );
                v___x_3941_ =
                    l_Lean_Syntax_node2(v___x_3929_, v___x_3930_, v___x_3936_, v___x_3940_);
                v___x_3942_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3942_, 0, v___x_3941_);
                lean_ctor_set(v___x_3942_, 1, v_a_3743_);
                return v___x_3942_;
            }
            6 => {
                v___x_3971_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_3972_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                lean_inc_n(v___x_3960_, 3);
                v___x_3973_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_3973_, 0, v___x_3960_);
                lean_ctor_set(v___x_3973_, 1, v___x_3972_);
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
                v___x_3977_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3977_, 0, v___x_3976_);
                lean_ctor_set(v___x_3977_, 1, v_a_3743_);
                return v___x_3977_;
            }
            7 => {
                lean_inc(v___x_4006_);
                v___x_4017_ =
                    l_Lean_Syntax_node2(v___x_4006_, v___x_4014_, v___y_4016_, v___x_4000_);
                v___x_4018_ =
                    l_Lean_Syntax_node2(v___x_4006_, v___x_4007_, v___x_4013_, v___x_4017_);
                v___x_4019_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4019_, 0, v___x_4018_);
                lean_ctor_set(v___x_4019_, 1, v_a_3743_);
                return v___x_4019_;
            }
            8 => {
                v___x_4048_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_4049_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                lean_inc_n(v___x_4037_, 3);
                v___x_4050_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4050_, 0, v___x_4037_);
                lean_ctor_set(v___x_4050_, 1, v___x_4049_);
                v___x_4051_ =
                    l_Lean_Syntax_node2(v___x_4037_, v___x_4048_, v___x_4050_, v___x_4000_);
                v___x_4052_ =
                    l_Lean_Syntax_node2(v___x_4037_, v___x_4045_, v___y_4047_, v___x_4051_);
                v___x_4053_ =
                    l_Lean_Syntax_node2(v___x_4037_, v___x_4038_, v___x_4044_, v___x_4052_);
                v___x_4054_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4054_, 0, v___x_4053_);
                lean_ctor_set(v___x_4054_, 1, v_a_3743_);
                return v___x_4054_;
            }
            9 => {
                lean_inc(v___x_4085_);
                v___x_4096_ = l_Lean_Syntax_node3(
                    v___x_4085_,
                    v___x_4093_,
                    v___x_4075_,
                    v___y_4095_,
                    v___x_4079_,
                );
                v___x_4097_ =
                    l_Lean_Syntax_node2(v___x_4085_, v___x_4086_, v___x_4092_, v___x_4096_);
                v___x_4098_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4098_, 0, v___x_4097_);
                lean_ctor_set(v___x_4098_, 1, v_a_3743_);
                return v___x_4098_;
            }
            10 => {
                v___x_4127_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_4128_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                lean_inc_n(v___x_4116_, 3);
                v___x_4129_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4129_, 0, v___x_4116_);
                lean_ctor_set(v___x_4129_, 1, v___x_4128_);
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
                v___x_4133_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4133_, 0, v___x_4132_);
                lean_ctor_set(v___x_4133_, 1, v_a_3743_);
                return v___x_4133_;
            }
            11 => {
                lean_inc(v___x_4162_);
                v___x_4173_ =
                    l_Lean_Syntax_node2(v___x_4162_, v___x_4170_, v___y_4172_, v___x_4161_);
                v___x_4174_ =
                    l_Lean_Syntax_node2(v___x_4162_, v___x_4163_, v___x_4169_, v___x_4173_);
                v___x_4175_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4175_, 0, v___x_4174_);
                lean_ctor_set(v___x_4175_, 1, v_a_3743_);
                return v___x_4175_;
            }
            12 => {
                lean_inc(v___x_4201_);
                v___x_4212_ =
                    l_Lean_Syntax_node2(v___x_4201_, v___x_4209_, v___y_4211_, v___x_4195_);
                v___x_4213_ =
                    l_Lean_Syntax_node2(v___x_4201_, v___x_4202_, v___x_4208_, v___x_4212_);
                v___x_4214_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4214_, 0, v___x_4213_);
                lean_ctor_set(v___x_4214_, 1, v_a_3743_);
                return v___x_4214_;
            }
            13 => {
                v___x_4244_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__31;
                v___x_4245_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__32;
                lean_inc_n(v___x_4233_, 3);
                v___x_4246_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4246_, 0, v___x_4233_);
                lean_ctor_set(v___x_4246_, 1, v___x_4245_);
                v___x_4247_ =
                    l_Lean_Syntax_node2(v___x_4233_, v___x_4244_, v___x_4246_, v___x_4195_);
                v___x_4248_ =
                    l_Lean_Syntax_node2(v___x_4233_, v___x_4241_, v___y_4243_, v___x_4247_);
                v___x_4249_ =
                    l_Lean_Syntax_node2(v___x_4233_, v___x_4234_, v___x_4240_, v___x_4248_);
                v___x_4250_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4250_, 0, v___x_4249_);
                lean_ctor_set(v___x_4250_, 1, v_a_3743_);
                return v___x_4250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed(
    mut v_x_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4268_: *mut LeanObject = core::ptr::null_mut();
    v_res_4268_ =
        l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro(v_x_4265_, v_a_4266_, v_a_4267_);
    lean_dec_ref(v_a_4266_);
    return v_res_4268_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(
    mut v_a_4269_: *mut LeanObject,
    mut v_b_4270_: *mut LeanObject,
    mut v_x_4271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4278_: u8 = 0;
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4271_) == 0 {
                    lean_dec(v_b_4270_);
                    lean_dec(v_a_4269_);
                    return v_x_4271_;
                } else {
                    v_key_4272_ = lean_ctor_get(v_x_4271_, 0);
                    v_value_4273_ = lean_ctor_get(v_x_4271_, 1);
                    v_tail_4274_ = lean_ctor_get(v_x_4271_, 2);
                    v_isSharedCheck_4286_ = (!lean_is_exclusive(v_x_4271_)) as u8;
                    if v_isSharedCheck_4286_ == 0 {
                        v___x_4276_ = v_x_4271_;
                        v_isShared_4277_ = v_isSharedCheck_4286_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4274_);
                        lean_inc(v_value_4273_);
                        lean_inc(v_key_4272_);
                        lean_dec(v_x_4271_);
                        v___x_4276_ = lean_box(0);
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
                        lean_ctor_set(v___x_4276_, 2, v___x_4279_);
                        v___x_4281_ = v___x_4276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_key_4272_);
                        lean_ctor_set(v_reuseFailAlloc_4282_, 1, v_value_4273_);
                        lean_ctor_set(v_reuseFailAlloc_4282_, 2, v___x_4279_);
                        v___x_4281_ = v_reuseFailAlloc_4282_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_4273_);
                    lean_dec(v_key_4272_);
                    if v_isShared_4277_ == 0 {
                        lean_ctor_set(v___x_4276_, 1, v_b_4270_);
                        lean_ctor_set(v___x_4276_, 0, v_a_4269_);
                        v___x_4284_ = v___x_4276_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4269_);
                        lean_ctor_set(v_reuseFailAlloc_4285_, 1, v_b_4270_);
                        lean_ctor_set(v_reuseFailAlloc_4285_, 2, v_tail_4274_);
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
    let mut v___x_4287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: u64 = 0;
    v___x_4287_ = lean_unsigned_to_nat(1723);
    v___x_4288_ = lean_uint64_of_nat(v___x_4287_);
    return v___x_4288_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(
    mut v_x_4289_: *mut LeanObject,
    mut v_x_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4297_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: u64 = 0;
    let mut v_hash_4318_: u64 = 0;
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4290_) == 0 {
                    return v_x_4289_;
                } else {
                    v_key_4291_ = lean_ctor_get(v_x_4290_, 0);
                    v_value_4292_ = lean_ctor_get(v_x_4290_, 1);
                    v_tail_4293_ = lean_ctor_get(v_x_4290_, 2);
                    v_isSharedCheck_4319_ = (!lean_is_exclusive(v_x_4290_)) as u8;
                    if v_isSharedCheck_4319_ == 0 {
                        v___x_4295_ = v_x_4290_;
                        v_isShared_4296_ = v_isSharedCheck_4319_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4293_);
                        lean_inc(v_value_4292_);
                        lean_inc(v_key_4291_);
                        lean_dec(v_x_4290_);
                        v___x_4295_ = lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4319_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4297_ = lean_array_get_size(v_x_4289_);
                if lean_obj_tag(v_key_4291_) == 0 {
                    v___x_4317_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4299_ = v___x_4317_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4318_ = lean_ctor_get_uint64(
                        v_key_4291_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                lean_inc(v___x_4311_);
                if v_isShared_4296_ == 0 {
                    lean_ctor_set(v___x_4295_, 2, v___x_4311_);
                    v___x_4313_ = v___x_4295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_key_4291_);
                    lean_ctor_set(v_reuseFailAlloc_4316_, 1, v_value_4292_);
                    lean_ctor_set(v_reuseFailAlloc_4316_, 2, v___x_4311_);
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
    mut v_i_4320_: *mut LeanObject,
    mut v_source_4321_: *mut LeanObject,
    mut v_target_4322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v_es_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4323_ = lean_array_get_size(v_source_4321_);
                v___x_4324_ = lean_nat_dec_lt(v_i_4320_, v___x_4323_);
                if v___x_4324_ == 0 {
                    lean_dec_ref(v_source_4321_);
                    lean_dec(v_i_4320_);
                    return v_target_4322_;
                } else {
                    v_es_4325_ = lean_array_fget(v_source_4321_, v_i_4320_);
                    v___x_4326_ = lean_box(0);
                    v_source_4327_ = lean_array_fset(v_source_4321_, v_i_4320_, v___x_4326_);
                    v_target_4328_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_target_4322_, v_es_4325_);
                    v___x_4329_ = lean_unsigned_to_nat(1);
                    v___x_4330_ = lean_nat_add(v_i_4320_, v___x_4329_);
                    lean_dec(v_i_4320_);
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
    mut v_data_4332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut LeanObject = core::ptr::null_mut();
    v___x_4333_ = lean_array_get_size(v_data_4332_);
    v___x_4334_ = lean_unsigned_to_nat(2);
    v_nbuckets_4335_ = lean_nat_mul(v___x_4333_, v___x_4334_);
    v___x_4336_ = lean_unsigned_to_nat(0);
    v___x_4337_ = lean_box(0);
    v___x_4338_ = lean_mk_array(v_nbuckets_4335_, v___x_4337_);
    v___x_4339_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v___x_4336_, v_data_4332_, v___x_4338_);
    return v___x_4339_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(
    mut v_a_4340_: *mut LeanObject,
    mut v_x_4341_: *mut LeanObject,
) -> u8 {
    let mut v___x_4342_: u8 = 0;
    let mut v_key_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4341_) == 0 {
                    v___x_4342_ = 0;
                    return v___x_4342_;
                } else {
                    v_key_4343_ = lean_ctor_get(v_x_4341_, 0);
                    v_tail_4344_ = lean_ctor_get(v_x_4341_, 2);
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
    mut v_a_4347_: *mut LeanObject,
    mut v_x_4348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4349_: u8 = 0;
    let mut v_r_4350_: *mut LeanObject = core::ptr::null_mut();
    v_res_4349_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_4347_, v_x_4348_);
    lean_dec(v_x_4348_);
    lean_dec(v_a_4347_);
    v_r_4350_ = lean_box((v_res_4349_) as usize);
    return v_r_4350_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(
    mut v_m_4351_: *mut LeanObject,
    mut v_a_4352_: *mut LeanObject,
    mut v_b_4353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: u8 = 0;
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v_val_4385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: u64 = 0;
    let mut v_hash_4400_: u64 = 0;
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4354_ = lean_ctor_get(v_m_4351_, 0);
                v_buckets_4355_ = lean_ctor_get(v_m_4351_, 1);
                v_isSharedCheck_4401_ = (!lean_is_exclusive(v_m_4351_)) as u8;
                if v_isSharedCheck_4401_ == 0 {
                    v___x_4357_ = v_m_4351_;
                    v_isShared_4358_ = v_isSharedCheck_4401_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_4355_);
                    lean_inc(v_size_4354_);
                    lean_dec(v_m_4351_);
                    v___x_4357_ = lean_box(0);
                    v_isShared_4358_ = v_isSharedCheck_4401_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4359_ = lean_array_get_size(v_buckets_4355_);
                if lean_obj_tag(v_a_4352_) == 0 {
                    v___x_4399_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4361_ = v___x_4399_;
                    state = 2;
                    continue;
                } else {
                    v_hash_4400_ = lean_ctor_get_uint64(
                        v_a_4352_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                    v___x_4375_ = lean_unsigned_to_nat(1);
                    v_size_x27_4376_ = lean_nat_add(v_size_4354_, v___x_4375_);
                    lean_dec(v_size_4354_);
                    lean_inc(v_bkt_4373_);
                    v___x_4377_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_4377_, 0, v_a_4352_);
                    lean_ctor_set(v___x_4377_, 1, v_b_4353_);
                    lean_ctor_set(v___x_4377_, 2, v_bkt_4373_);
                    v_buckets_x27_4378_ =
                        lean_array_uset(v_buckets_4355_, v___x_4372_, v___x_4377_);
                    v___x_4379_ = lean_unsigned_to_nat(4);
                    v___x_4380_ = lean_nat_mul(v_size_x27_4376_, v___x_4379_);
                    v___x_4381_ = lean_unsigned_to_nat(3);
                    v___x_4382_ = lean_nat_div(v___x_4380_, v___x_4381_);
                    lean_dec(v___x_4380_);
                    v___x_4383_ = lean_array_get_size(v_buckets_x27_4378_);
                    v___x_4384_ = lean_nat_dec_le(v___x_4382_, v___x_4383_);
                    lean_dec(v___x_4382_);
                    if v___x_4384_ == 0 {
                        v_val_4385_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_buckets_x27_4378_);
                        if v_isShared_4358_ == 0 {
                            lean_ctor_set(v___x_4357_, 1, v_val_4385_);
                            lean_ctor_set(v___x_4357_, 0, v_size_x27_4376_);
                            v___x_4387_ = v___x_4357_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4388_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_size_x27_4376_);
                            lean_ctor_set(v_reuseFailAlloc_4388_, 1, v_val_4385_);
                            v___x_4387_ = v_reuseFailAlloc_4388_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_4358_ == 0 {
                            lean_ctor_set(v___x_4357_, 1, v_buckets_x27_4378_);
                            lean_ctor_set(v___x_4357_, 0, v_size_x27_4376_);
                            v___x_4390_ = v___x_4357_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4391_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_size_x27_4376_);
                            lean_ctor_set(v_reuseFailAlloc_4391_, 1, v_buckets_x27_4378_);
                            v___x_4390_ = v_reuseFailAlloc_4391_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_4373_);
                    v___x_4392_ = lean_box(0);
                    v_buckets_x27_4393_ =
                        lean_array_uset(v_buckets_4355_, v___x_4372_, v___x_4392_);
                    v___x_4394_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_4352_, v_b_4353_, v_bkt_4373_);
                    v___x_4395_ = lean_array_uset(v_buckets_x27_4393_, v___x_4372_, v___x_4394_);
                    if v_isShared_4358_ == 0 {
                        lean_ctor_set(v___x_4357_, 1, v___x_4395_);
                        v___x_4397_ = v___x_4357_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4398_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4398_, 0, v_size_4354_);
                        lean_ctor_set(v_reuseFailAlloc_4398_, 1, v___x_4395_);
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
    mut v_as_x27_4402_: *mut LeanObject,
    mut v_b_4403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4402_) == 0 {
                    return v_b_4403_;
                } else {
                    v_head_4404_ = lean_ctor_get(v_as_x27_4402_, 0);
                    v_tail_4405_ = lean_ctor_get(v_as_x27_4402_, 1);
                    v_fst_4406_ = lean_ctor_get(v_head_4404_, 0);
                    v_snd_4407_ = lean_ctor_get(v_head_4404_, 1);
                    lean_inc(v_snd_4407_);
                    lean_inc(v_fst_4406_);
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
    mut v_as_x27_4410_: *mut LeanObject,
    mut v_b_4411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4412_: *mut LeanObject = core::ptr::null_mut();
    v_res_4412_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_4410_, v_b_4411_);
    lean_dec(v_as_x27_4410_);
    return v_res_4412_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(
    mut v_m_4413_: *mut LeanObject,
    mut v_l_4414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4415_: *mut LeanObject = core::ptr::null_mut();
    v___x_4415_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_l_4414_, v_m_4413_);
    return v___x_4415_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0___boxed(
    mut v_m_4416_: *mut LeanObject,
    mut v_l_4417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4418_: *mut LeanObject = core::ptr::null_mut();
    v_res_4418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0(v_m_4416_, v_l_4417_);
    lean_dec(v_l_4417_);
    return v_res_4418_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22()
-> *mut LeanObject {
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    v___x_4481_ = lean_box(0);
    v___x_4482_ = lean_unsigned_to_nat(16);
    v___x_4483_ = lean_mk_array(v___x_4482_, v___x_4481_);
    return v___x_4483_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23()
-> *mut LeanObject {
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    v___x_4484_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22_once), _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__22);
    v___x_4485_ = lean_unsigned_to_nat(0);
    v___x_4486_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4486_, 0, v___x_4485_);
    lean_ctor_set(v___x_4486_, 1, v___x_4484_);
    return v___x_4486_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24()
-> *mut LeanObject {
    let mut v___x_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut LeanObject = core::ptr::null_mut();
    v___x_4487_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23_once), _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__23);
    v___x_4488_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__21;
    v___x_4489_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v___x_4488_, v___x_4487_);
    return v___x_4489_;
}
pub unsafe fn _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap()
-> *mut LeanObject {
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    v___x_4490_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24), core::ptr::addr_of_mut!(l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24_once), _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap___closed__24);
    return v___x_4490_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0(
    mut v_00_u03b2_4491_: *mut LeanObject,
    mut v_m_4492_: *mut LeanObject,
    mut v_a_4493_: *mut LeanObject,
    mut v_b_4494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    v___x_4495_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0___redArg(v_m_4492_, v_a_4493_, v_b_4494_);
    return v___x_4495_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(
    mut v_as_4496_: *mut LeanObject,
    mut v_as_x27_4497_: *mut LeanObject,
    mut v_b_4498_: *mut LeanObject,
    mut v_a_4499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4500_: *mut LeanObject = core::ptr::null_mut();
    v___x_4500_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___redArg(v_as_x27_4497_, v_b_4498_);
    return v___x_4500_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1___boxed(
    mut v_as_4501_: *mut LeanObject,
    mut v_as_x27_4502_: *mut LeanObject,
    mut v_b_4503_: *mut LeanObject,
    mut v_a_4504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4505_: *mut LeanObject = core::ptr::null_mut();
    v_res_4505_ = l_List_forIn_x27_loop___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__1(v_as_4501_, v_as_x27_4502_, v_b_4503_, v_a_4504_);
    lean_dec(v_as_x27_4502_);
    lean_dec(v_as_4501_);
    return v_res_4505_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4506_: *mut LeanObject,
    mut v_a_4507_: *mut LeanObject,
    mut v_x_4508_: *mut LeanObject,
) -> u8 {
    let mut v___x_4509_: u8 = 0;
    v___x_4509_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___redArg(v_a_4507_, v_x_4508_);
    return v___x_4509_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4510_: *mut LeanObject,
    mut v_a_4511_: *mut LeanObject,
    mut v_x_4512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4513_: u8 = 0;
    let mut v_r_4514_: *mut LeanObject = core::ptr::null_mut();
    v_res_4513_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__1(v_00_u03b2_4510_, v_a_4511_, v_x_4512_);
    lean_dec(v_x_4512_);
    lean_dec(v_a_4511_);
    v_r_4514_ = lean_box((v_res_4513_) as usize);
    return v_r_4514_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4515_: *mut LeanObject,
    mut v_data_4516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    v___x_4517_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2___redArg(v_data_4516_);
    return v___x_4517_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3(
    mut v_00_u03b2_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
    mut v_b_4520_: *mut LeanObject,
    mut v_x_4521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    v___x_4522_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__3___redArg(v_a_4519_, v_b_4520_, v_x_4521_);
    return v___x_4522_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_4523_: *mut LeanObject,
    mut v_i_4524_: *mut LeanObject,
    mut v_source_4525_: *mut LeanObject,
    mut v_target_4526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4527_: *mut LeanObject = core::ptr::null_mut();
    v___x_4527_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3___redArg(v_i_4524_, v_source_4525_, v_target_4526_);
    return v___x_4527_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5(
    mut v_00_u03b2_4528_: *mut LeanObject,
    mut v_x_4529_: *mut LeanObject,
    mut v_x_4530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    v___x_4531_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_x_4529_, v_x_4530_);
    return v___x_4531_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(
    mut v_name_4532_: *mut LeanObject,
    mut v___y_4533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut LeanObject = core::ptr::null_mut();
    v___x_4535_ = lean_st_ref_get(v___y_4533_);
    v_env_4536_ = lean_ctor_get(v___x_4535_, 0);
    lean_inc_ref(v_env_4536_);
    lean_dec(v___x_4535_);
    v___x_4537_ = l_Lean_errorExplanationExt;
    v_toEnvExtension_4538_ = lean_ctor_get(v___x_4537_, 0);
    v_asyncMode_4539_ = lean_ctor_get(v_toEnvExtension_4538_, 2);
    v___x_4540_ = lean_box(1);
    v___x_4541_ = lean_box(0);
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
    lean_dec(v___x_4542_);
    v___x_4544_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4544_, 0, v___x_4543_);
    return v___x_4544_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg___boxed(
    mut v_name_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4548_: *mut LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_4545_, v___y_4546_);
    lean_dec(v___y_4546_);
    lean_dec(v_name_4545_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(
    mut v_name_4549_: *mut LeanObject,
    mut v___y_4550_: *mut LeanObject,
    mut v___y_4551_: *mut LeanObject,
    mut v___y_4552_: *mut LeanObject,
    mut v___y_4553_: *mut LeanObject,
    mut v___y_4554_: *mut LeanObject,
    mut v___y_4555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4557_: *mut LeanObject = core::ptr::null_mut();
    v___x_4557_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v_name_4549_, v___y_4555_);
    return v___x_4557_;
}
pub unsafe fn l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___boxed(
    mut v_name_4558_: *mut LeanObject,
    mut v___y_4559_: *mut LeanObject,
    mut v___y_4560_: *mut LeanObject,
    mut v___y_4561_: *mut LeanObject,
    mut v___y_4562_: *mut LeanObject,
    mut v___y_4563_: *mut LeanObject,
    mut v___y_4564_: *mut LeanObject,
    mut v___y_4565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4566_: *mut LeanObject = core::ptr::null_mut();
    v_res_4566_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3(v_name_4558_, v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_, v___y_4563_, v___y_4564_);
    lean_dec(v___y_4564_);
    lean_dec_ref(v___y_4563_);
    lean_dec(v___y_4562_);
    lean_dec_ref(v___y_4561_);
    lean_dec(v___y_4560_);
    lean_dec_ref(v___y_4559_);
    lean_dec(v_name_4558_);
    return v_res_4566_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(
    mut v_msgData_4567_: *mut LeanObject,
    mut v___y_4568_: *mut LeanObject,
    mut v___y_4569_: *mut LeanObject,
    mut v___y_4570_: *mut LeanObject,
    mut v___y_4571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    v___x_4573_ = lean_st_ref_get(v___y_4571_);
    v_env_4574_ = lean_ctor_get(v___x_4573_, 0);
    lean_inc_ref(v_env_4574_);
    lean_dec(v___x_4573_);
    v___x_4575_ = lean_st_ref_get(v___y_4569_);
    v_mctx_4576_ = lean_ctor_get(v___x_4575_, 0);
    lean_inc_ref(v_mctx_4576_);
    lean_dec(v___x_4575_);
    v_lctx_4577_ = lean_ctor_get(v___y_4568_, 2);
    v_options_4578_ = lean_ctor_get(v___y_4570_, 2);
    lean_inc_ref(v_options_4578_);
    lean_inc_ref(v_lctx_4577_);
    v___x_4579_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4579_, 0, v_env_4574_);
    lean_ctor_set(v___x_4579_, 1, v_mctx_4576_);
    lean_ctor_set(v___x_4579_, 2, v_lctx_4577_);
    lean_ctor_set(v___x_4579_, 3, v_options_4578_);
    v___x_4580_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4580_, 0, v___x_4579_);
    lean_ctor_set(v___x_4580_, 1, v_msgData_4567_);
    v___x_4581_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4581_, 0, v___x_4580_);
    return v___x_4581_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18___boxed(
    mut v_msgData_4582_: *mut LeanObject,
    mut v___y_4583_: *mut LeanObject,
    mut v___y_4584_: *mut LeanObject,
    mut v___y_4585_: *mut LeanObject,
    mut v___y_4586_: *mut LeanObject,
    mut v___y_4587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4588_: *mut LeanObject = core::ptr::null_mut();
    v_res_4588_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msgData_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
    lean_dec(v___y_4586_);
    lean_dec_ref(v___y_4585_);
    lean_dec(v___y_4584_);
    lean_dec_ref(v___y_4583_);
    return v_res_4588_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: f64 = 0.0;
    v___x_4589_ = lean_unsigned_to_nat(0);
    v___x_4590_ = lean_float_of_nat(v___x_4589_);
    return v___x_4590_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(
    mut v_cls_4594_: *mut LeanObject,
    mut v_msg_4595_: *mut LeanObject,
    mut v___y_4596_: *mut LeanObject,
    mut v___y_4597_: *mut LeanObject,
    mut v___y_4598_: *mut LeanObject,
    mut v___y_4599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4606_: u8 = 0;
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4619_: u8 = 0;
    let mut v_tid_4620_: u64 = 0;
    let mut v_traces_4621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4624_: u8 = 0;
    let mut v___x_4625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4626_: f64 = 0.0;
    let mut v___x_4627_: u8 = 0;
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4645_: u8 = 0;
    let mut v_isSharedCheck_4646_: u8 = 0;
    let mut v_isSharedCheck_4647_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4601_ = lean_ctor_get(v___y_4598_, 5);
                v___x_4602_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_4595_, v___y_4596_, v___y_4597_, v___y_4598_, v___y_4599_);
                v_a_4603_ = lean_ctor_get(v___x_4602_, 0);
                v_isSharedCheck_4647_ = (!lean_is_exclusive(v___x_4602_)) as u8;
                if v_isSharedCheck_4647_ == 0 {
                    v___x_4605_ = v___x_4602_;
                    v_isShared_4606_ = v_isSharedCheck_4647_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4603_);
                    lean_dec(v___x_4602_);
                    v___x_4605_ = lean_box(0);
                    v_isShared_4606_ = v_isSharedCheck_4647_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4607_ = lean_st_ref_take(v___y_4599_);
                v_traceState_4608_ = lean_ctor_get(v___x_4607_, 4);
                v_env_4609_ = lean_ctor_get(v___x_4607_, 0);
                v_nextMacroScope_4610_ = lean_ctor_get(v___x_4607_, 1);
                v_ngen_4611_ = lean_ctor_get(v___x_4607_, 2);
                v_auxDeclNGen_4612_ = lean_ctor_get(v___x_4607_, 3);
                v_cache_4613_ = lean_ctor_get(v___x_4607_, 5);
                v_messages_4614_ = lean_ctor_get(v___x_4607_, 6);
                v_infoState_4615_ = lean_ctor_get(v___x_4607_, 7);
                v_snapshotTasks_4616_ = lean_ctor_get(v___x_4607_, 8);
                v_isSharedCheck_4646_ = (!lean_is_exclusive(v___x_4607_)) as u8;
                if v_isSharedCheck_4646_ == 0 {
                    v___x_4618_ = v___x_4607_;
                    v_isShared_4619_ = v_isSharedCheck_4646_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4616_);
                    lean_inc(v_infoState_4615_);
                    lean_inc(v_messages_4614_);
                    lean_inc(v_cache_4613_);
                    lean_inc(v_traceState_4608_);
                    lean_inc(v_auxDeclNGen_4612_);
                    lean_inc(v_ngen_4611_);
                    lean_inc(v_nextMacroScope_4610_);
                    lean_inc(v_env_4609_);
                    lean_dec(v___x_4607_);
                    v___x_4618_ = lean_box(0);
                    v_isShared_4619_ = v_isSharedCheck_4646_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_4620_ = lean_ctor_get_uint64(
                    v_traceState_4608_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4621_ = lean_ctor_get(v_traceState_4608_, 0);
                v_isSharedCheck_4645_ = (!lean_is_exclusive(v_traceState_4608_)) as u8;
                if v_isSharedCheck_4645_ == 0 {
                    v___x_4623_ = v_traceState_4608_;
                    v_isShared_4624_ = v_isSharedCheck_4645_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_4621_);
                    lean_dec(v_traceState_4608_);
                    v___x_4623_ = lean_box(0);
                    v_isShared_4624_ = v_isSharedCheck_4645_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4625_ = lean_box(0);
                v___x_4626_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
                v___x_4627_ = 0;
                v___x_4628_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                v___x_4629_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4629_, 0, v_cls_4594_);
                lean_ctor_set(v___x_4629_, 1, v___x_4625_);
                lean_ctor_set(v___x_4629_, 2, v___x_4628_);
                lean_ctor_set_float(
                    v___x_4629_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4626_,
                );
                lean_ctor_set_float(
                    v___x_4629_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4626_,
                );
                lean_ctor_set_uint8(
                    v___x_4629_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4627_,
                );
                v___x_4630_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2;
                v___x_4631_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4631_, 0, v___x_4629_);
                lean_ctor_set(v___x_4631_, 1, v_a_4603_);
                lean_ctor_set(v___x_4631_, 2, v___x_4630_);
                lean_inc(v_ref_4601_);
                v___x_4632_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4632_, 0, v_ref_4601_);
                lean_ctor_set(v___x_4632_, 1, v___x_4631_);
                v___x_4633_ = l_Lean_PersistentArray_push___redArg(v_traces_4621_, v___x_4632_);
                if v_isShared_4624_ == 0 {
                    lean_ctor_set(v___x_4623_, 0, v___x_4633_);
                    v___x_4635_ = v___x_4623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4644_, 0, v___x_4633_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4644_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4620_,
                    );
                    v___x_4635_ = v_reuseFailAlloc_4644_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_4619_ == 0 {
                    lean_ctor_set(v___x_4618_, 4, v___x_4635_);
                    v___x_4637_ = v___x_4618_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_env_4609_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 1, v_nextMacroScope_4610_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 2, v_ngen_4611_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 3, v_auxDeclNGen_4612_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 4, v___x_4635_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 5, v_cache_4613_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 6, v_messages_4614_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 7, v_infoState_4615_);
                    lean_ctor_set(v_reuseFailAlloc_4643_, 8, v_snapshotTasks_4616_);
                    v___x_4637_ = v_reuseFailAlloc_4643_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4638_ = lean_st_ref_set(v___y_4599_, v___x_4637_);
                v___x_4639_ = lean_box(0);
                if v_isShared_4606_ == 0 {
                    lean_ctor_set(v___x_4605_, 0, v___x_4639_);
                    v___x_4641_ = v___x_4605_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4642_, 0, v___x_4639_);
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
    mut v_cls_4648_: *mut LeanObject,
    mut v_msg_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
    mut v___y_4653_: *mut LeanObject,
    mut v___y_4654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4655_: *mut LeanObject = core::ptr::null_mut();
    v_res_4655_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_4648_, v_msg_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
    lean_dec(v___y_4653_);
    lean_dec_ref(v___y_4652_);
    lean_dec(v___y_4651_);
    lean_dec_ref(v___y_4650_);
    return v_res_4655_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(
    mut v_as_4659_: *mut LeanObject,
    mut v___y_4660_: *mut LeanObject,
    mut v___y_4661_: *mut LeanObject,
    mut v___y_4662_: *mut LeanObject,
    mut v___y_4663_: *mut LeanObject,
    mut v___y_4664_: *mut LeanObject,
    mut v___y_4665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4670_: u8 = 0;
    let mut v_tail_4671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: u8 = 0;
    let mut v___x_4682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_4659_) == 0 {
                    v___x_4667_ = lean_box(0);
                    v___x_4668_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4668_, 0, v___x_4667_);
                    return v___x_4668_;
                } else {
                    v_options_4669_ = lean_ctor_get(v___y_4664_, 2);
                    v_hasTrace_4670_ = lean_ctor_get_uint8(
                        v_options_4669_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4670_ == 0 {
                        v_tail_4671_ = lean_ctor_get(v_as_4659_, 1);
                        lean_inc(v_tail_4671_);
                        lean_dec_ref_known(v_as_4659_, 2);
                        v_as_4659_ = v_tail_4671_;
                        state = 0;
                        continue;
                    } else {
                        v_head_4673_ = lean_ctor_get(v_as_4659_, 0);
                        lean_inc(v_head_4673_);
                        v_tail_4674_ = lean_ctor_get(v_as_4659_, 1);
                        lean_inc(v_tail_4674_);
                        lean_dec_ref_known(v_as_4659_, 2);
                        v_fst_4675_ = lean_ctor_get(v_head_4673_, 0);
                        lean_inc_n(v_fst_4675_, 2);
                        v_snd_4676_ = lean_ctor_get(v_head_4673_, 1);
                        lean_inc(v_snd_4676_);
                        lean_dec(v_head_4673_);
                        v_inheritedTraceOptions_4677_ = lean_ctor_get(v___y_4664_, 13);
                        v___x_4678_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1;
                        v___x_4679_ = l_Lean_Name_append(v___x_4678_, v_fst_4675_);
                        v___x_4680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4677_,
                            v_options_4669_,
                            v___x_4679_,
                        );
                        lean_dec(v___x_4679_);
                        if v___x_4680_ == 0 {
                            lean_dec(v_snd_4676_);
                            lean_dec(v_fst_4675_);
                            v_as_4659_ = v_tail_4674_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4682_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_4682_, 0, v_snd_4676_);
                            v___x_4683_ = l_Lean_MessageData_ofFormat(v___x_4682_);
                            v___x_4684_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_fst_4675_, v___x_4683_, v___y_4662_, v___y_4663_, v___y_4664_, v___y_4665_);
                            if lean_obj_tag(v___x_4684_) == 0 {
                                lean_dec_ref_known(v___x_4684_, 1);
                                v_as_4659_ = v_tail_4674_;
                                state = 0;
                                continue;
                            } else {
                                lean_dec(v_tail_4674_);
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
    mut v_as_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4694_: *mut LeanObject = core::ptr::null_mut();
    v_res_4694_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v_as_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
    lean_dec(v___y_4692_);
    lean_dec_ref(v___y_4691_);
    lean_dec(v___y_4690_);
    lean_dec_ref(v___y_4689_);
    lean_dec(v___y_4688_);
    lean_dec_ref(v___y_4687_);
    return v_res_4694_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut LeanObject = core::ptr::null_mut();
    v___x_4695_ = lean_box(0);
    v___x_4696_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_4697_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_4697_, 0, v___x_4696_);
    lean_ctor_set(v___x_4697_, 1, v___x_4695_);
    return v___x_4697_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg()
-> *mut LeanObject {
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut LeanObject = core::ptr::null_mut();
    v___x_4699_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
    v___x_4700_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4700_, 0, v___x_4699_);
    return v___x_4700_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___boxed(
    mut v___y_4701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4702_: *mut LeanObject = core::ptr::null_mut();
    v_res_4702_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
    return v_res_4702_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut LeanObject = core::ptr::null_mut();
    v___x_4708_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4709_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_4709_, 0, v___x_4708_);
    return v___x_4709_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_4710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    v___x_4710_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__3);
    v___x_4711_ = l_Lean_MessageData_ofFormat(v___x_4710_);
    return v___x_4711_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_4712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut LeanObject = core::ptr::null_mut();
    v___x_4712_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__4);
    v___x_4713_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__2;
    v___x_4714_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_4714_, 0, v___x_4713_);
    lean_ctor_set(v___x_4714_, 1, v___x_4712_);
    return v___x_4714_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(
    mut v_ref_4715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    v___x_4717_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___closed__5);
    v___x_4718_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4718_, 0, v_ref_4715_);
    lean_ctor_set(v___x_4718_, 1, v___x_4717_);
    v___x_4719_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4719_, 0, v___x_4718_);
    return v___x_4719_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg___boxed(
    mut v_ref_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4722_: *mut LeanObject = core::ptr::null_mut();
    v_res_4722_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_4720_);
    return v_res_4722_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(
    mut v_env_4723_: *mut LeanObject,
    mut v_declName_4724_: *mut LeanObject,
    mut v___y_4725_: *mut LeanObject,
    mut v___y_4726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4727_: u8 = 0;
    let mut v_env_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: u8 = 0;
    let mut v___x_4731_: u8 = 0;
    v___x_4727_ = 0;
    v_env_4728_ = l_Lean_Environment_setExporting(v_env_4723_, v___x_4727_);
    lean_inc(v_declName_4724_);
    v___x_4729_ = l_Lean_mkPrivateName(v_env_4728_, v_declName_4724_);
    v___x_4730_ = 1;
    lean_inc_ref(v_env_4728_);
    v___x_4731_ = l_Lean_Environment_contains(v_env_4728_, v___x_4729_, v___x_4730_);
    if v___x_4731_ == 0 {
        let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4733_: u8 = 0;
        let mut v___x_4734_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
        v___x_4732_ = l_Lean_privateToUserName(v_declName_4724_);
        v___x_4733_ = l_Lean_Environment_contains(v_env_4728_, v___x_4732_, v___x_4730_);
        v___x_4734_ = lean_box((v___x_4733_) as usize);
        v___x_4735_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4735_, 0, v___x_4734_);
        lean_ctor_set(v___x_4735_, 1, v___y_4726_);
        return v___x_4735_;
    } else {
        let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_env_4728_);
        lean_dec(v_declName_4724_);
        v___x_4736_ = lean_box((v___x_4731_) as usize);
        v___x_4737_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4737_, 0, v___x_4736_);
        lean_ctor_set(v___x_4737_, 1, v___y_4726_);
        return v___x_4737_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed(
    mut v_env_4738_: *mut LeanObject,
    mut v_declName_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4742_: *mut LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1(v_env_4738_, v_declName_4739_, v___y_4740_, v___y_4741_);
    lean_dec_ref(v___y_4740_);
    return v_res_4742_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(
    mut v_x_4743_: *mut LeanObject,
    mut v___y_4744_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_4743_) == 0 {
        let mut v_a_4745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4746_: *mut LeanObject = core::ptr::null_mut();
        v_a_4745_ = lean_ctor_get(v_x_4743_, 0);
        lean_inc(v_a_4745_);
        v___x_4746_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_4746_, 0, v_a_4745_);
        lean_ctor_set(v___x_4746_, 1, v___y_4744_);
        return v___x_4746_;
    } else {
        let mut v_a_4747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
        v_a_4747_ = lean_ctor_get(v_x_4743_, 0);
        lean_inc(v_a_4747_);
        v___x_4748_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_4748_, 0, v_a_4747_);
        lean_ctor_set(v___x_4748_, 1, v___y_4744_);
        return v___x_4748_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg___boxed(
    mut v_x_4749_: *mut LeanObject,
    mut v___y_4750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4751_: *mut LeanObject = core::ptr::null_mut();
    v_res_4751_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_4749_, v___y_4750_);
    lean_dec_ref(v_x_4749_);
    return v_res_4751_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(
    mut v_env_4752_: *mut LeanObject,
    mut v_stx_4753_: *mut LeanObject,
    mut v___y_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4766_: u8 = 0;
    let mut v_unused_4767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4771_: u8 = 0;
    let mut v_snd_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4777_: u8 = 0;
    let mut v___x_4779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4782_: u8 = 0;
    let mut v_a_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4787_: u8 = 0;
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4795_: u8 = 0;
    let mut v_isSharedCheck_4796_: u8 = 0;
    let mut v_a_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4801_: u8 = 0;
    let mut v___x_4803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4804_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4756_) == 0 {
                    v_a_4757_ = lean_ctor_get(v___x_4756_, 0);
                    lean_inc(v_a_4757_);
                    if lean_obj_tag(v_a_4757_) == 0 {
                        v_a_4758_ = lean_ctor_get(v___x_4756_, 1);
                        v_isSharedCheck_4766_ = (!lean_is_exclusive(v___x_4756_)) as u8;
                        if v_isSharedCheck_4766_ == 0 {
                            v_unused_4767_ = lean_ctor_get(v___x_4756_, 0);
                            lean_dec(v_unused_4767_);
                            v___x_4760_ = v___x_4756_;
                            v_isShared_4761_ = v_isSharedCheck_4766_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4758_);
                            lean_dec(v___x_4756_);
                            v___x_4760_ = lean_box(0);
                            v_isShared_4761_ = v_isSharedCheck_4766_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_4768_ = lean_ctor_get(v_a_4757_, 0);
                        v_isSharedCheck_4796_ = (!lean_is_exclusive(v_a_4757_)) as u8;
                        if v_isSharedCheck_4796_ == 0 {
                            v___x_4770_ = v_a_4757_;
                            v_isShared_4771_ = v_isSharedCheck_4796_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_4768_);
                            lean_dec(v_a_4757_);
                            v___x_4770_ = lean_box(0);
                            v_isShared_4771_ = v_isSharedCheck_4796_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4797_ = lean_ctor_get(v___x_4756_, 0);
                    v_a_4798_ = lean_ctor_get(v___x_4756_, 1);
                    v_isSharedCheck_4805_ = (!lean_is_exclusive(v___x_4756_)) as u8;
                    if v_isSharedCheck_4805_ == 0 {
                        v___x_4800_ = v___x_4756_;
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4798_);
                        lean_inc(v_a_4797_);
                        lean_dec(v___x_4756_);
                        v___x_4800_ = lean_box(0);
                        v_isShared_4801_ = v_isSharedCheck_4805_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4762_ = lean_box(0);
                if v_isShared_4761_ == 0 {
                    lean_ctor_set(v___x_4760_, 0, v___x_4762_);
                    v___x_4764_ = v___x_4760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4765_, 0, v___x_4762_);
                    lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_a_4758_);
                    v___x_4764_ = v_reuseFailAlloc_4765_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4764_;
            }
            3 => {
                v_snd_4772_ = lean_ctor_get(v_val_4768_, 1);
                lean_inc(v_snd_4772_);
                lean_dec(v_val_4768_);
                if lean_obj_tag(v_snd_4772_) == 0 {
                    lean_del_object(v___x_4770_);
                    v_a_4773_ = lean_ctor_get(v___x_4756_, 1);
                    lean_inc(v_a_4773_);
                    lean_dec_ref_known(v___x_4756_, 2);
                    v_a_4774_ = lean_ctor_get(v_snd_4772_, 0);
                    v_isSharedCheck_4782_ = (!lean_is_exclusive(v_snd_4772_)) as u8;
                    if v_isSharedCheck_4782_ == 0 {
                        v___x_4776_ = v_snd_4772_;
                        v_isShared_4777_ = v_isSharedCheck_4782_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4774_);
                        lean_dec(v_snd_4772_);
                        v___x_4776_ = lean_box(0);
                        v_isShared_4777_ = v_isSharedCheck_4782_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4783_ = lean_ctor_get(v___x_4756_, 1);
                    lean_inc(v_a_4783_);
                    lean_dec_ref_known(v___x_4756_, 2);
                    v_a_4784_ = lean_ctor_get(v_snd_4772_, 0);
                    v_isSharedCheck_4795_ = (!lean_is_exclusive(v_snd_4772_)) as u8;
                    if v_isSharedCheck_4795_ == 0 {
                        v___x_4786_ = v_snd_4772_;
                        v_isShared_4787_ = v_isSharedCheck_4795_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4784_);
                        lean_dec(v_snd_4772_);
                        v___x_4786_ = lean_box(0);
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
                    v_reuseFailAlloc_4781_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4781_, 0, v_a_4774_);
                    v___x_4779_ = v_reuseFailAlloc_4781_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4780_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_4779_, v_a_4773_);
                lean_dec_ref(v___x_4779_);
                return v___x_4780_;
            }
            6 => {
                if v_isShared_4771_ == 0 {
                    lean_ctor_set(v___x_4770_, 0, v_a_4784_);
                    v___x_4789_ = v___x_4770_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4794_, 0, v_a_4784_);
                    v___x_4789_ = v_reuseFailAlloc_4794_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4787_ == 0 {
                    lean_ctor_set(v___x_4786_, 0, v___x_4789_);
                    v___x_4791_ = v___x_4786_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4793_, 0, v___x_4789_);
                    v___x_4791_ = v_reuseFailAlloc_4793_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4792_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v___x_4791_, v_a_4783_);
                lean_dec_ref(v___x_4791_);
                return v___x_4792_;
            }
            9 => {
                if v_isShared_4801_ == 0 {
                    v___x_4803_ = v___x_4800_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4804_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4804_, 0, v_a_4797_);
                    lean_ctor_set(v_reuseFailAlloc_4804_, 1, v_a_4798_);
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
    mut v_env_4806_: *mut LeanObject,
    mut v_stx_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4810_: *mut LeanObject = core::ptr::null_mut();
    v_res_4810_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0(v_env_4806_, v_stx_4807_, v___y_4808_, v___y_4809_);
    lean_dec_ref(v___y_4808_);
    return v_res_4810_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(
    mut v_env_4811_: *mut LeanObject,
    mut v_options_4812_: *mut LeanObject,
    mut v_currNamespace_4813_: *mut LeanObject,
    mut v_openDecls_4814_: *mut LeanObject,
    mut v_n_4815_: *mut LeanObject,
    mut v___y_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut LeanObject = core::ptr::null_mut();
    v___x_4818_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_4811_,
        v_options_4812_,
        v_currNamespace_4813_,
        v_openDecls_4814_,
        v_n_4815_,
    );
    v___x_4819_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4819_, 0, v___x_4818_);
    lean_ctor_set(v___x_4819_, 1, v___y_4817_);
    return v___x_4819_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed(
    mut v_env_4820_: *mut LeanObject,
    mut v_options_4821_: *mut LeanObject,
    mut v_currNamespace_4822_: *mut LeanObject,
    mut v_openDecls_4823_: *mut LeanObject,
    mut v_n_4824_: *mut LeanObject,
    mut v___y_4825_: *mut LeanObject,
    mut v___y_4826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4827_: *mut LeanObject = core::ptr::null_mut();
    v_res_4827_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4(v_env_4820_, v_options_4821_, v_currNamespace_4822_, v_openDecls_4823_, v_n_4824_, v___y_4825_, v___y_4826_);
    lean_dec_ref(v___y_4825_);
    lean_dec_ref(v_options_4821_);
    return v_res_4827_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(
    mut v_currNamespace_4828_: *mut LeanObject,
    mut v___y_4829_: *mut LeanObject,
    mut v___y_4830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4831_: *mut LeanObject = core::ptr::null_mut();
    v___x_4831_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4831_, 0, v_currNamespace_4828_);
    lean_ctor_set(v___x_4831_, 1, v___y_4830_);
    return v___x_4831_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed(
    mut v_currNamespace_4832_: *mut LeanObject,
    mut v___y_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4835_: *mut LeanObject = core::ptr::null_mut();
    v_res_4835_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3(v_currNamespace_4832_, v___y_4833_, v___y_4834_);
    lean_dec_ref(v___y_4833_);
    return v_res_4835_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(
    mut v_a_4836_: *mut LeanObject,
    mut v_x_4837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: u8 = 0;
    let mut v___x_4844_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4837_) == 0 {
                    v___x_4838_ = lean_box(0);
                    return v___x_4838_;
                } else {
                    v_key_4839_ = lean_ctor_get(v_x_4837_, 0);
                    v_value_4840_ = lean_ctor_get(v_x_4837_, 1);
                    v_tail_4841_ = lean_ctor_get(v_x_4837_, 2);
                    v___x_4842_ = lean_name_eq(v_key_4839_, v_a_4836_);
                    if v___x_4842_ == 0 {
                        v_x_4837_ = v_tail_4841_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_4840_);
                        v___x_4844_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4844_, 0, v_value_4840_);
                        return v___x_4844_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg___boxed(
    mut v_a_4845_: *mut LeanObject,
    mut v_x_4846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4847_: *mut LeanObject = core::ptr::null_mut();
    v_res_4847_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_4845_, v_x_4846_);
    lean_dec(v_x_4846_);
    lean_dec(v_a_4845_);
    return v_res_4847_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(
    mut v_m_4848_: *mut LeanObject,
    mut v_a_4849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: u64 = 0;
    let mut v_hash_4868_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4850_ = lean_ctor_get(v_m_4848_, 1);
                v___x_4851_ = lean_array_get_size(v_buckets_4850_);
                if lean_obj_tag(v_a_4849_) == 0 {
                    v___x_4867_ = lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_DHashMap_Internal_Raw_u2080_Const_insertMany___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___closed__0);
                    v___y_4853_ = v___x_4867_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4868_ = lean_ctor_get_uint64(
                        v_a_4849_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_m_4869_: *mut LeanObject,
    mut v_a_4870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4871_: *mut LeanObject = core::ptr::null_mut();
    v_res_4871_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_4869_, v_a_4870_);
    lean_dec(v_a_4870_);
    lean_dec_ref(v_m_4869_);
    return v_res_4871_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(
    mut v_keys_4872_: *mut LeanObject,
    mut v_i_4873_: *mut LeanObject,
    mut v_k_4874_: *mut LeanObject,
) -> u8 {
    let mut v___x_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: u8 = 0;
    let mut v_k_x27_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4878_: u8 = 0;
    let mut v___x_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4875_ = lean_array_get_size(v_keys_4872_);
                v___x_4876_ = lean_nat_dec_lt(v_i_4873_, v___x_4875_);
                if v___x_4876_ == 0 {
                    lean_dec(v_i_4873_);
                    return v___x_4876_;
                } else {
                    v_k_x27_4877_ = lean_array_fget_borrowed(v_keys_4872_, v_i_4873_);
                    v___x_4878_ = l_Lean_instBEqExtraModUse_beq(v_k_4874_, v_k_x27_4877_);
                    if v___x_4878_ == 0 {
                        v___x_4879_ = lean_unsigned_to_nat(1);
                        v___x_4880_ = lean_nat_add(v_i_4873_, v___x_4879_);
                        lean_dec(v_i_4873_);
                        v_i_4873_ = v___x_4880_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4873_);
                        return v___x_4878_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg___boxed(
    mut v_keys_4882_: *mut LeanObject,
    mut v_i_4883_: *mut LeanObject,
    mut v_k_4884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4885_: u8 = 0;
    let mut v_r_4886_: *mut LeanObject = core::ptr::null_mut();
    v_res_4885_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_4882_, v_i_4883_, v_k_4884_);
    lean_dec_ref(v_k_4884_);
    lean_dec_ref(v_keys_4882_);
    v_r_4886_ = lean_box((v_res_4885_) as usize);
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
    v___x_4891_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__0);
    v___x_4892_ = lean_usize_sub(v___x_4891_, v___x_4890_);
    return v___x_4892_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(
    mut v_x_4893_: *mut LeanObject,
    mut v_x_4894_: usize,
    mut v_x_4895_: *mut LeanObject,
) -> u8 {
    let mut v_es_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: usize = 0;
    let mut v___x_4899_: usize = 0;
    let mut v___x_4900_: usize = 0;
    let mut v_j_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: u8 = 0;
    let mut v_node_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: usize = 0;
    let mut v___x_4908_: u8 = 0;
    let mut v_ks_4909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4893_) == 0 {
                    v_es_4896_ = lean_ctor_get(v_x_4893_, 0);
                    v___x_4897_ = lean_box(2);
                    v___x_4898_ = 5usize;
                    v___x_4899_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___closed__1);
                    v___x_4900_ = lean_usize_land(v_x_4894_, v___x_4899_);
                    v_j_4901_ = lean_usize_to_nat(v___x_4900_);
                    v___x_4902_ = lean_array_get_borrowed(v___x_4897_, v_es_4896_, v_j_4901_);
                    lean_dec(v_j_4901_);
                    match lean_obj_tag(v___x_4902_) {
                        0 => {
                            v_key_4903_ = lean_ctor_get(v___x_4902_, 0);
                            v___x_4904_ = l_Lean_instBEqExtraModUse_beq(v_x_4895_, v_key_4903_);
                            return v___x_4904_;
                        }
                        1 => {
                            v_node_4905_ = lean_ctor_get(v___x_4902_, 0);
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
                    v_ks_4909_ = lean_ctor_get(v_x_4893_, 0);
                    v___x_4910_ = lean_unsigned_to_nat(0);
                    v___x_4911_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_ks_4909_, v___x_4910_, v_x_4895_);
                    return v___x_4911_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg___boxed(
    mut v_x_4912_: *mut LeanObject,
    mut v_x_4913_: *mut LeanObject,
    mut v_x_4914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_20467__boxed_4915_: usize = 0;
    let mut v_res_4916_: u8 = 0;
    let mut v_r_4917_: *mut LeanObject = core::ptr::null_mut();
    v_x_20467__boxed_4915_ = lean_unbox_usize(v_x_4913_);
    lean_dec(v_x_4913_);
    v_res_4916_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_4912_, v_x_20467__boxed_4915_, v_x_4914_);
    lean_dec_ref(v_x_4914_);
    lean_dec_ref(v_x_4912_);
    v_r_4917_ = lean_box((v_res_4916_) as usize);
    return v_r_4917_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(
    mut v_x_4918_: *mut LeanObject,
    mut v_x_4919_: *mut LeanObject,
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
    mut v_x_4923_: *mut LeanObject,
    mut v_x_4924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4925_: u8 = 0;
    let mut v_r_4926_: *mut LeanObject = core::ptr::null_mut();
    v_res_4925_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_4923_, v_x_4924_);
    lean_dec_ref(v_x_4924_);
    lean_dec_ref(v_x_4923_);
    v_r_4926_ = lean_box((v_res_4925_) as usize);
    return v_r_4926_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut LeanObject = core::ptr::null_mut();
    v___x_4929_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__1;
    v___x_4930_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__0;
    v___x_4931_ =
        l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), v___x_4930_, v___x_4929_);
    return v___x_4931_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3()
-> *mut LeanObject {
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    v___x_4932_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4932_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4()
-> *mut LeanObject {
    let mut v___x_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    v___x_4933_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__3);
    v___x_4934_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4934_, 0, v___x_4933_);
    return v___x_4934_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5()
-> *mut LeanObject {
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    v___x_4935_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
    v___x_4936_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4936_, 0, v___x_4935_);
    lean_ctor_set(v___x_4936_, 1, v___x_4935_);
    return v___x_4936_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6()
-> *mut LeanObject {
    let mut v___x_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    v___x_4937_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__4);
    v___x_4938_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_4938_, 0, v___x_4937_);
    lean_ctor_set(v___x_4938_, 1, v___x_4937_);
    lean_ctor_set(v___x_4938_, 2, v___x_4937_);
    lean_ctor_set(v___x_4938_, 3, v___x_4937_);
    lean_ctor_set(v___x_4938_, 4, v___x_4937_);
    lean_ctor_set(v___x_4938_, 5, v___x_4937_);
    return v___x_4938_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10()
-> *mut LeanObject {
    let mut v___x_4943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    v___x_4943_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__9;
    v___x_4944_ = l_Lean_stringToMessageData(v___x_4943_);
    return v___x_4944_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12()
-> *mut LeanObject {
    let mut v___x_4946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    v___x_4946_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__11;
    v___x_4947_ = l_Lean_stringToMessageData(v___x_4946_);
    return v___x_4947_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13()
-> *mut LeanObject {
    let mut v___x_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    v___x_4948_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
    v___x_4949_ = l_Lean_stringToMessageData(v___x_4948_);
    return v___x_4949_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14()
-> *mut LeanObject {
    let mut v_cls_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    v_cls_4950_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
    v___x_4951_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4___closed__1;
    v___x_4952_ = l_Lean_Name_append(v___x_4951_, v_cls_4950_);
    return v___x_4952_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16()
-> *mut LeanObject {
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    v___x_4954_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__15;
    v___x_4955_ = l_Lean_stringToMessageData(v___x_4954_);
    return v___x_4955_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18()
-> *mut LeanObject {
    let mut v___x_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut LeanObject = core::ptr::null_mut();
    v___x_4957_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__17;
    v___x_4958_ = l_Lean_stringToMessageData(v___x_4957_);
    return v___x_4958_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(
    mut v_mod_4963_: *mut LeanObject,
    mut v_isMeta_4964_: u8,
    mut v_hint_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
    mut v___y_4968_: *mut LeanObject,
    mut v___y_4969_: *mut LeanObject,
    mut v___y_4970_: *mut LeanObject,
    mut v___y_4971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4975_: u8 = 0;
    let mut v___x_4976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4998_: u8 = 0;
    let mut v_asyncMode_4999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_5008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5012_: u8 = 0;
    let mut v___x_5013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5020_: u8 = 0;
    let mut v_unused_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5023_: u8 = 0;
    let mut v_unused_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: u8 = 0;
    let mut v_options_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_5028_: u8 = 0;
    let mut v_inheritedTraceOptions_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cls_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: u8 = 0;
    let mut v___x_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: u8 = 0;
    let mut v___x_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4973_ = lean_st_ref_get(v___y_4971_);
                v_env_4974_ = lean_ctor_get(v___x_4973_, 0);
                lean_inc_ref(v_env_4974_);
                lean_dec(v___x_4973_);
                v_isExporting_4975_ = lean_ctor_get_uint8(
                    v_env_4974_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_4974_);
                v___x_4976_ = lean_st_ref_get(v___y_4971_);
                v_env_4977_ = lean_ctor_get(v___x_4976_, 0);
                lean_inc_ref(v_env_4977_);
                lean_dec(v___x_4976_);
                v___x_4978_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
                lean_inc(v_mod_4963_);
                v_entry_4979_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_4979_, 0, v_mod_4963_);
                lean_ctor_set_uint8(
                    v_entry_4979_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_4975_,
                );
                lean_ctor_set_uint8(
                    v_entry_4979_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4964_,
                );
                v___x_4980_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4981_ = lean_box(1);
                v___x_4982_ = lean_box(0);
                v___x_5025_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4978_,
                    v___x_4980_,
                    v_env_4977_,
                    v___x_4981_,
                    v___x_4982_,
                );
                v___x_5026_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_5025_, v_entry_4979_);
                lean_dec(v___x_5025_);
                if v___x_5026_ == 0 {
                    v_options_5027_ = lean_ctor_get(v___y_4970_, 2);
                    v_hasTrace_5028_ = lean_ctor_get_uint8(
                        v_options_5027_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_5028_ == 0 {
                        lean_dec(v_hint_4965_);
                        lean_dec(v_mod_4963_);
                        v___y_4984_ = v___y_4969_;
                        v___y_4985_ = v___y_4971_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_5029_ = lean_ctor_get(v___y_4970_, 13);
                        v_cls_5030_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
                        v___x_5050_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
                        v___x_5051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_5029_,
                            v_options_5027_,
                            v___x_5050_,
                        );
                        if v___x_5051_ == 0 {
                            lean_dec(v_hint_4965_);
                            lean_dec(v_mod_4963_);
                            v___y_4984_ = v___y_4969_;
                            v___y_4985_ = v___y_4971_;
                            state = 1;
                            continue;
                        } else {
                            v___x_5052_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
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
                    lean_dec_ref_known(v_entry_4979_, 1);
                    lean_dec(v_hint_4965_);
                    lean_dec(v_mod_4963_);
                    v___x_5063_ = lean_box(0);
                    v___x_5064_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5064_, 0, v___x_5063_);
                    return v___x_5064_;
                }
            }
            1 => {
                v___x_4986_ = lean_st_ref_take(v___y_4985_);
                v_toEnvExtension_4987_ = lean_ctor_get(v___x_4980_, 0);
                v_env_4988_ = lean_ctor_get(v___x_4986_, 0);
                v_nextMacroScope_4989_ = lean_ctor_get(v___x_4986_, 1);
                v_ngen_4990_ = lean_ctor_get(v___x_4986_, 2);
                v_auxDeclNGen_4991_ = lean_ctor_get(v___x_4986_, 3);
                v_traceState_4992_ = lean_ctor_get(v___x_4986_, 4);
                v_messages_4993_ = lean_ctor_get(v___x_4986_, 6);
                v_infoState_4994_ = lean_ctor_get(v___x_4986_, 7);
                v_snapshotTasks_4995_ = lean_ctor_get(v___x_4986_, 8);
                v_isSharedCheck_5023_ = (!lean_is_exclusive(v___x_4986_)) as u8;
                if v_isSharedCheck_5023_ == 0 {
                    v_unused_5024_ = lean_ctor_get(v___x_4986_, 5);
                    lean_dec(v_unused_5024_);
                    v___x_4997_ = v___x_4986_;
                    v_isShared_4998_ = v_isSharedCheck_5023_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4995_);
                    lean_inc(v_infoState_4994_);
                    lean_inc(v_messages_4993_);
                    lean_inc(v_traceState_4992_);
                    lean_inc(v_auxDeclNGen_4991_);
                    lean_inc(v_ngen_4990_);
                    lean_inc(v_nextMacroScope_4989_);
                    lean_inc(v_env_4988_);
                    lean_dec(v___x_4986_);
                    v___x_4997_ = lean_box(0);
                    v_isShared_4998_ = v_isSharedCheck_5023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4999_ = lean_ctor_get(v_toEnvExtension_4987_, 2);
                v___x_5000_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4980_,
                    v_env_4988_,
                    v_entry_4979_,
                    v_asyncMode_4999_,
                    v___x_4982_,
                );
                v___x_5001_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__5);
                if v_isShared_4998_ == 0 {
                    lean_ctor_set(v___x_4997_, 5, v___x_5001_);
                    lean_ctor_set(v___x_4997_, 0, v___x_5000_);
                    v___x_5003_ = v___x_4997_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5022_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 0, v___x_5000_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 1, v_nextMacroScope_4989_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 2, v_ngen_4990_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 3, v_auxDeclNGen_4991_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 4, v_traceState_4992_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 5, v___x_5001_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 6, v_messages_4993_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 7, v_infoState_4994_);
                    lean_ctor_set(v_reuseFailAlloc_5022_, 8, v_snapshotTasks_4995_);
                    v___x_5003_ = v_reuseFailAlloc_5022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5004_ = lean_st_ref_set(v___y_4985_, v___x_5003_);
                v___x_5005_ = lean_st_ref_take(v___y_4984_);
                v_mctx_5006_ = lean_ctor_get(v___x_5005_, 0);
                v_zetaDeltaFVarIds_5007_ = lean_ctor_get(v___x_5005_, 2);
                v_postponed_5008_ = lean_ctor_get(v___x_5005_, 3);
                v_diag_5009_ = lean_ctor_get(v___x_5005_, 4);
                v_isSharedCheck_5020_ = (!lean_is_exclusive(v___x_5005_)) as u8;
                if v_isSharedCheck_5020_ == 0 {
                    v_unused_5021_ = lean_ctor_get(v___x_5005_, 1);
                    lean_dec(v_unused_5021_);
                    v___x_5011_ = v___x_5005_;
                    v_isShared_5012_ = v_isSharedCheck_5020_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_diag_5009_);
                    lean_inc(v_postponed_5008_);
                    lean_inc(v_zetaDeltaFVarIds_5007_);
                    lean_inc(v_mctx_5006_);
                    lean_dec(v___x_5005_);
                    v___x_5011_ = lean_box(0);
                    v_isShared_5012_ = v_isSharedCheck_5020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__6);
                if v_isShared_5012_ == 0 {
                    lean_ctor_set(v___x_5011_, 1, v___x_5013_);
                    v___x_5015_ = v___x_5011_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5019_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5019_, 0, v_mctx_5006_);
                    lean_ctor_set(v_reuseFailAlloc_5019_, 1, v___x_5013_);
                    lean_ctor_set(v_reuseFailAlloc_5019_, 2, v_zetaDeltaFVarIds_5007_);
                    lean_ctor_set(v_reuseFailAlloc_5019_, 3, v_postponed_5008_);
                    lean_ctor_set(v_reuseFailAlloc_5019_, 4, v_diag_5009_);
                    v___x_5015_ = v_reuseFailAlloc_5019_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5016_ = lean_st_ref_set(v___y_4984_, v___x_5015_);
                v___x_5017_ = lean_box(0);
                v___x_5018_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5018_, 0, v___x_5017_);
                return v___x_5018_;
            }
            6 => {
                v___x_5034_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5034_, 0, v___y_5032_);
                lean_ctor_set(v___x_5034_, 1, v___y_5033_);
                v___x_5035_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_5030_, v___x_5034_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_);
                if lean_obj_tag(v___x_5035_) == 0 {
                    lean_dec_ref_known(v___x_5035_, 1);
                    v___y_4984_ = v___y_4969_;
                    v___y_4985_ = v___y_4971_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_4979_, 1);
                    return v___x_5035_;
                }
            }
            7 => {
                lean_inc_ref(v___y_5038_);
                v___x_5039_ = l_Lean_stringToMessageData(v___y_5038_);
                v___x_5040_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5040_, 0, v___y_5037_);
                lean_ctor_set(v___x_5040_, 1, v___x_5039_);
                v___x_5041_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
                v___x_5042_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5042_, 0, v___x_5040_);
                lean_ctor_set(v___x_5042_, 1, v___x_5041_);
                v___x_5043_ = l_Lean_MessageData_ofName(v_mod_4963_);
                v___x_5044_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5044_, 0, v___x_5042_);
                lean_ctor_set(v___x_5044_, 1, v___x_5043_);
                v___x_5045_ = l_Lean_Name_isAnonymous(v_hint_4965_);
                if v___x_5045_ == 0 {
                    v___x_5046_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
                    v___x_5047_ = l_Lean_MessageData_ofName(v_hint_4965_);
                    v___x_5048_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5048_, 0, v___x_5046_);
                    lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                    v___y_5032_ = v___x_5044_;
                    v___y_5033_ = v___x_5048_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_hint_4965_);
                    v___x_5049_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
                    v___y_5032_ = v___x_5044_;
                    v___y_5033_ = v___x_5049_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                lean_inc_ref(v___y_5054_);
                v___x_5055_ = l_Lean_stringToMessageData(v___y_5054_);
                v___x_5056_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5056_, 0, v___x_5052_);
                lean_ctor_set(v___x_5056_, 1, v___x_5055_);
                v___x_5057_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
                v___x_5058_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5058_, 0, v___x_5056_);
                lean_ctor_set(v___x_5058_, 1, v___x_5057_);
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
    mut v_mod_5065_: *mut LeanObject,
    mut v_isMeta_5066_: *mut LeanObject,
    mut v_hint_5067_: *mut LeanObject,
    mut v___y_5068_: *mut LeanObject,
    mut v___y_5069_: *mut LeanObject,
    mut v___y_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
    mut v___y_5074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_5075_: u8 = 0;
    let mut v_res_5076_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5075_ = (lean_unbox(v_isMeta_5066_) as u8);
    v_res_5076_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_mod_5065_, v_isMeta_boxed_5075_, v_hint_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
    lean_dec(v___y_5073_);
    lean_dec_ref(v___y_5072_);
    lean_dec(v___y_5071_);
    lean_dec_ref(v___y_5070_);
    lean_dec(v___y_5069_);
    lean_dec_ref(v___y_5068_);
    return v_res_5076_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(
    mut v___x_5077_: *mut LeanObject,
    mut v_declName_5078_: *mut LeanObject,
    mut v_as_5079_: *mut LeanObject,
    mut v_sz_5080_: usize,
    mut v_i_5081_: usize,
    mut v_b_5082_: *mut LeanObject,
    mut v___y_5083_: *mut LeanObject,
    mut v___y_5084_: *mut LeanObject,
    mut v___y_5085_: *mut LeanObject,
    mut v___y_5086_: *mut LeanObject,
    mut v___y_5087_: *mut LeanObject,
    mut v___y_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5090_: u8 = 0;
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: u8 = 0;
    let mut v___x_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: usize = 0;
    let mut v___x_5103_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5090_ = lean_usize_dec_lt(v_i_5081_, v_sz_5080_);
                if v___x_5090_ == 0 {
                    lean_dec(v_declName_5078_);
                    v___x_5091_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5091_, 0, v_b_5082_);
                    return v___x_5091_;
                } else {
                    v___x_5092_ = l_Lean_Environment_header(v___x_5077_);
                    v_modules_5093_ = lean_ctor_get(v___x_5092_, 3);
                    lean_inc_ref(v_modules_5093_);
                    lean_dec_ref(v___x_5092_);
                    v___x_5094_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_5095_ = lean_array_uget_borrowed(v_as_5079_, v_i_5081_);
                    v___x_5096_ = lean_array_get(v___x_5094_, v_modules_5093_, v_a_5095_);
                    lean_dec_ref(v_modules_5093_);
                    v_toImport_5097_ = lean_ctor_get(v___x_5096_, 0);
                    lean_inc_ref(v_toImport_5097_);
                    lean_dec(v___x_5096_);
                    v_module_5098_ = lean_ctor_get(v_toImport_5097_, 0);
                    lean_inc(v_module_5098_);
                    lean_dec_ref(v_toImport_5097_);
                    v___x_5099_ = 0;
                    lean_inc(v_declName_5078_);
                    v___x_5100_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_5098_, v___x_5099_, v_declName_5078_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
                    if lean_obj_tag(v___x_5100_) == 0 {
                        lean_dec_ref_known(v___x_5100_, 1);
                        v___x_5101_ = lean_box(0);
                        v___x_5102_ = 1usize;
                        v___x_5103_ = lean_usize_add(v_i_5081_, v___x_5102_);
                        v_i_5081_ = v___x_5103_;
                        v_b_5082_ = v___x_5101_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_5078_);
                        return v___x_5100_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5___boxed(
    mut v___x_5105_: *mut LeanObject,
    mut v_declName_5106_: *mut LeanObject,
    mut v_as_5107_: *mut LeanObject,
    mut v_sz_5108_: *mut LeanObject,
    mut v_i_5109_: *mut LeanObject,
    mut v_b_5110_: *mut LeanObject,
    mut v___y_5111_: *mut LeanObject,
    mut v___y_5112_: *mut LeanObject,
    mut v___y_5113_: *mut LeanObject,
    mut v___y_5114_: *mut LeanObject,
    mut v___y_5115_: *mut LeanObject,
    mut v___y_5116_: *mut LeanObject,
    mut v___y_5117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5118_: usize = 0;
    let mut v_i_boxed_5119_: usize = 0;
    let mut v_res_5120_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5118_ = lean_unbox_usize(v_sz_5108_);
    lean_dec(v_sz_5108_);
    v_i_boxed_5119_ = lean_unbox_usize(v_i_5109_);
    lean_dec(v_i_5109_);
    v_res_5120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v___x_5105_, v_declName_5106_, v_as_5107_, v_sz_boxed_5118_, v_i_boxed_5119_, v_b_5110_, v___y_5111_, v___y_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
    lean_dec(v___y_5116_);
    lean_dec_ref(v___y_5115_);
    lean_dec(v___y_5114_);
    lean_dec_ref(v___y_5113_);
    lean_dec(v___y_5112_);
    lean_dec_ref(v___y_5111_);
    lean_dec_ref(v_as_5107_);
    lean_dec_ref(v___x_5105_);
    return v_res_5120_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut LeanObject = core::ptr::null_mut();
    v___x_5123_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__1;
    v___x_5124_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__0;
    v___x_5125_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_5124_, v___x_5123_);
    return v___x_5125_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(
    mut v_declName_5128_: *mut LeanObject,
    mut v_isMeta_5129_: u8,
    mut v___y_5130_: *mut LeanObject,
    mut v___y_5131_: *mut LeanObject,
    mut v___y_5132_: *mut LeanObject,
    mut v___y_5133_: *mut LeanObject,
    mut v___y_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5145_: usize = 0;
    let mut v___x_5146_: usize = 0;
    let mut v___x_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5150_: u8 = 0;
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5154_: u8 = 0;
    let mut v_unused_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5161_: u8 = 0;
    let mut v___x_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5167_: u8 = 0;
    let mut v_toImport_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: u8 = 0;
    let mut v___x_5179_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5137_ = lean_st_ref_get(v___y_5135_);
                v_env_5141_ = lean_ctor_get(v___x_5137_, 0);
                lean_inc_ref(v_env_5141_);
                lean_dec(v___x_5137_);
                v___x_5156_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_5141_, v_declName_5128_);
                if lean_obj_tag(v___x_5156_) == 0 {
                    lean_dec_ref(v_env_5141_);
                    lean_dec(v_declName_5128_);
                    state = 1;
                    continue;
                } else {
                    v_val_5157_ = lean_ctor_get(v___x_5156_, 0);
                    lean_inc(v_val_5157_);
                    lean_dec_ref_known(v___x_5156_, 1);
                    v___x_5158_ = l_Lean_Environment_header(v_env_5141_);
                    v_modules_5159_ = lean_ctor_get(v___x_5158_, 3);
                    lean_inc_ref(v_modules_5159_);
                    lean_dec_ref(v___x_5158_);
                    v___x_5160_ = lean_array_get_size(v_modules_5159_);
                    v___x_5161_ = lean_nat_dec_lt(v_val_5157_, v___x_5160_);
                    if v___x_5161_ == 0 {
                        lean_dec_ref(v_modules_5159_);
                        lean_dec(v_val_5157_);
                        lean_dec_ref(v_env_5141_);
                        lean_dec(v_declName_5128_);
                        state = 1;
                        continue;
                    } else {
                        v___x_5162_ = lean_st_ref_get(v___y_5135_);
                        v_env_5163_ = lean_ctor_get(v___x_5162_, 0);
                        lean_inc_ref(v_env_5163_);
                        lean_dec(v___x_5162_);
                        v___x_5164_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
                        v___x_5165_ = lean_array_fget(v_modules_5159_, v_val_5157_);
                        lean_dec(v_val_5157_);
                        lean_dec_ref(v_modules_5159_);
                        if v_isMeta_5129_ == 0 {
                            lean_dec_ref(v_env_5163_);
                            v___y_5167_ = v_isMeta_5129_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_5128_);
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
                v___x_5139_ = lean_box(0);
                v___x_5140_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5140_, 0, v___x_5139_);
                return v___x_5140_;
            }
            2 => {
                v___x_5144_ = lean_box(0);
                v_sz_5145_ = lean_array_size(v___y_5143_);
                v___x_5146_ = 0usize;
                v___x_5147_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__5(v_env_5141_, v_declName_5128_, v___y_5143_, v_sz_5145_, v___x_5146_, v___x_5144_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
                lean_dec_ref(v___y_5143_);
                lean_dec_ref(v_env_5141_);
                if lean_obj_tag(v___x_5147_) == 0 {
                    v_isSharedCheck_5154_ = (!lean_is_exclusive(v___x_5147_)) as u8;
                    if v_isSharedCheck_5154_ == 0 {
                        v_unused_5155_ = lean_ctor_get(v___x_5147_, 0);
                        lean_dec(v_unused_5155_);
                        v___x_5149_ = v___x_5147_;
                        v_isShared_5150_ = v_isSharedCheck_5154_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5147_);
                        v___x_5149_ = lean_box(0);
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
                    lean_ctor_set(v___x_5149_, 0, v___x_5144_);
                    v___x_5152_ = v___x_5149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5153_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5153_, 0, v___x_5144_);
                    v___x_5152_ = v_reuseFailAlloc_5153_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5152_;
            }
            5 => {
                v_toImport_5168_ = lean_ctor_get(v___x_5165_, 0);
                lean_inc_ref(v_toImport_5168_);
                lean_dec(v___x_5165_);
                v_module_5169_ = lean_ctor_get(v_toImport_5168_, 0);
                lean_inc(v_module_5169_);
                lean_dec_ref(v_toImport_5168_);
                lean_inc(v_declName_5128_);
                v___x_5170_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4(v_module_5169_, v___y_5167_, v_declName_5128_, v___y_5130_, v___y_5131_, v___y_5132_, v___y_5133_, v___y_5134_, v___y_5135_);
                if lean_obj_tag(v___x_5170_) == 0 {
                    lean_dec_ref_known(v___x_5170_, 1);
                    v___x_5171_ = l_Lean_indirectModUseExt;
                    v___x_5172_ = lean_box(1);
                    v___x_5173_ = lean_box(0);
                    lean_inc_ref(v_env_5141_);
                    v___x_5174_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_5164_,
                        v___x_5171_,
                        v_env_5141_,
                        v___x_5172_,
                        v___x_5173_,
                    );
                    v___x_5175_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_5174_, v_declName_5128_);
                    lean_dec(v___x_5174_);
                    if lean_obj_tag(v___x_5175_) == 0 {
                        v___x_5176_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3;
                        v___y_5143_ = v___x_5176_;
                        state = 2;
                        continue;
                    } else {
                        v_val_5177_ = lean_ctor_get(v___x_5175_, 0);
                        lean_inc(v_val_5177_);
                        lean_dec_ref_known(v___x_5175_, 1);
                        v___y_5143_ = v_val_5177_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_5141_);
                    lean_dec(v_declName_5128_);
                    return v___x_5170_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___boxed(
    mut v_declName_5180_: *mut LeanObject,
    mut v_isMeta_5181_: *mut LeanObject,
    mut v___y_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
    mut v___y_5184_: *mut LeanObject,
    mut v___y_5185_: *mut LeanObject,
    mut v___y_5186_: *mut LeanObject,
    mut v___y_5187_: *mut LeanObject,
    mut v___y_5188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_5189_: u8 = 0;
    let mut v_res_5190_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_5189_ = (lean_unbox(v_isMeta_5181_) as u8);
    v_res_5190_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_declName_5180_, v_isMeta_boxed_5189_, v___y_5182_, v___y_5183_, v___y_5184_, v___y_5185_, v___y_5186_, v___y_5187_);
    lean_dec(v___y_5187_);
    lean_dec_ref(v___y_5186_);
    lean_dec(v___y_5185_);
    lean_dec_ref(v___y_5184_);
    lean_dec(v___y_5183_);
    lean_dec_ref(v___y_5182_);
    return v_res_5190_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(
    mut v_as_x27_5191_: *mut LeanObject,
    mut v_b_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
    mut v___y_5195_: *mut LeanObject,
    mut v___y_5196_: *mut LeanObject,
    mut v___y_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: u8 = 0;
    let mut v___x_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_5191_) == 0 {
                    v___x_5200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5200_, 0, v_b_5192_);
                    return v___x_5200_;
                } else {
                    v_head_5201_ = lean_ctor_get(v_as_x27_5191_, 0);
                    v_tail_5202_ = lean_ctor_get(v_as_x27_5191_, 1);
                    v___x_5203_ = 1;
                    lean_inc(v_head_5201_);
                    v___x_5204_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2(v_head_5201_, v___x_5203_, v___y_5193_, v___y_5194_, v___y_5195_, v___y_5196_, v___y_5197_, v___y_5198_);
                    if lean_obj_tag(v___x_5204_) == 0 {
                        lean_dec_ref_known(v___x_5204_, 1);
                        v___x_5205_ = lean_box(0);
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
    mut v_as_x27_5207_: *mut LeanObject,
    mut v_b_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
    mut v___y_5210_: *mut LeanObject,
    mut v___y_5211_: *mut LeanObject,
    mut v___y_5212_: *mut LeanObject,
    mut v___y_5213_: *mut LeanObject,
    mut v___y_5214_: *mut LeanObject,
    mut v___y_5215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5216_: *mut LeanObject = core::ptr::null_mut();
    v_res_5216_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_5207_, v_b_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_, v___y_5214_);
    lean_dec(v___y_5214_);
    lean_dec_ref(v___y_5213_);
    lean_dec(v___y_5212_);
    lean_dec_ref(v___y_5211_);
    lean_dec(v___y_5210_);
    lean_dec_ref(v___y_5209_);
    lean_dec(v_as_x27_5207_);
    return v_res_5216_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(
    mut v_env_5217_: *mut LeanObject,
    mut v_currNamespace_5218_: *mut LeanObject,
    mut v_openDecls_5219_: *mut LeanObject,
    mut v_n_5220_: *mut LeanObject,
    mut v___y_5221_: *mut LeanObject,
    mut v___y_5222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    v___x_5223_ = l_Lean_ResolveName_resolveNamespace(
        v_env_5217_,
        v_currNamespace_5218_,
        v_openDecls_5219_,
        v_n_5220_,
    );
    v___x_5224_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_5224_, 0, v___x_5223_);
    lean_ctor_set(v___x_5224_, 1, v___y_5222_);
    return v___x_5224_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed(
    mut v_env_5225_: *mut LeanObject,
    mut v_currNamespace_5226_: *mut LeanObject,
    mut v_openDecls_5227_: *mut LeanObject,
    mut v_n_5228_: *mut LeanObject,
    mut v___y_5229_: *mut LeanObject,
    mut v___y_5230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5231_: *mut LeanObject = core::ptr::null_mut();
    v_res_5231_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2(v_env_5225_, v_currNamespace_5226_, v_openDecls_5227_, v_n_5228_, v___y_5229_, v___y_5230_);
    lean_dec_ref(v___y_5229_);
    return v_res_5231_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0()
-> *mut LeanObject {
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    v___x_5232_ = lean_box(1);
    v___x_5233_ = l_Lean_MessageData_ofFormat(v___x_5232_);
    return v___x_5233_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3()
-> *mut LeanObject {
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut LeanObject = core::ptr::null_mut();
    v___x_5237_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__2;
    v___x_5238_ = l_Lean_MessageData_ofFormat(v___x_5237_);
    return v___x_5238_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(
    mut v_x_5239_: *mut LeanObject,
    mut v_x_5240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_5241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5245_: u8 = 0;
    let mut v_before_5246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v_unused_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5264_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5240_) == 0 {
                    return v_x_5239_;
                } else {
                    v_head_5241_ = lean_ctor_get(v_x_5240_, 0);
                    v_tail_5242_ = lean_ctor_get(v_x_5240_, 1);
                    v_isSharedCheck_5264_ = (!lean_is_exclusive(v_x_5240_)) as u8;
                    if v_isSharedCheck_5264_ == 0 {
                        v___x_5244_ = v_x_5240_;
                        v_isShared_5245_ = v_isSharedCheck_5264_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5242_);
                        lean_inc(v_head_5241_);
                        lean_dec(v_x_5240_);
                        v___x_5244_ = lean_box(0);
                        v_isShared_5245_ = v_isSharedCheck_5264_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_5246_ = lean_ctor_get(v_head_5241_, 0);
                v_isSharedCheck_5262_ = (!lean_is_exclusive(v_head_5241_)) as u8;
                if v_isSharedCheck_5262_ == 0 {
                    v_unused_5263_ = lean_ctor_get(v_head_5241_, 1);
                    lean_dec(v_unused_5263_);
                    v___x_5248_ = v_head_5241_;
                    v_isShared_5249_ = v_isSharedCheck_5262_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_before_5246_);
                    lean_dec(v_head_5241_);
                    v___x_5248_ = lean_box(0);
                    v_isShared_5249_ = v_isSharedCheck_5262_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5250_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
                if v_isShared_5249_ == 0 {
                    lean_ctor_set_tag(v___x_5248_, 7);
                    lean_ctor_set(v___x_5248_, 1, v___x_5250_);
                    lean_ctor_set(v___x_5248_, 0, v_x_5239_);
                    v___x_5252_ = v___x_5248_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_x_5239_);
                    lean_ctor_set(v_reuseFailAlloc_5261_, 1, v___x_5250_);
                    v___x_5252_ = v_reuseFailAlloc_5261_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5253_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__3);
                if v_isShared_5245_ == 0 {
                    lean_ctor_set_tag(v___x_5244_, 7);
                    lean_ctor_set(v___x_5244_, 1, v___x_5253_);
                    lean_ctor_set(v___x_5244_, 0, v___x_5252_);
                    v___x_5255_ = v___x_5244_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5260_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5260_, 0, v___x_5252_);
                    lean_ctor_set(v_reuseFailAlloc_5260_, 1, v___x_5253_);
                    v___x_5255_ = v_reuseFailAlloc_5260_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5256_ = l_Lean_MessageData_ofSyntax(v_before_5246_);
                v___x_5257_ = l_Lean_indentD(v___x_5256_);
                v___x_5258_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5258_, 0, v___x_5255_);
                lean_ctor_set(v___x_5258_, 1, v___x_5257_);
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
    mut v_opts_5265_: *mut LeanObject,
    mut v_opt_5266_: *mut LeanObject,
) -> u8 {
    let mut v_name_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defValue_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_5269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    v_name_5267_ = lean_ctor_get(v_opt_5266_, 0);
    v_defValue_5268_ = lean_ctor_get(v_opt_5266_, 1);
    v_map_5269_ = lean_ctor_get(v_opts_5265_, 0);
    v___x_5270_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_5269_,
            v_name_5267_,
        );
    if lean_obj_tag(v___x_5270_) == 0 {
        let mut v___x_5271_: u8 = 0;
        v___x_5271_ = (lean_unbox(v_defValue_5268_) as u8);
        return v___x_5271_;
    } else {
        let mut v_val_5272_: *mut LeanObject = core::ptr::null_mut();
        v_val_5272_ = lean_ctor_get(v___x_5270_, 0);
        lean_inc(v_val_5272_);
        lean_dec_ref_known(v___x_5270_, 1);
        if lean_obj_tag(v_val_5272_) == 1 {
            let mut v_v_5273_: u8 = 0;
            v_v_5273_ = lean_ctor_get_uint8(v_val_5272_, 0 as u32);
            lean_dec_ref_known(v_val_5272_, 0);
            return v_v_5273_;
        } else {
            let mut v___x_5274_: u8 = 0;
            lean_dec(v_val_5272_);
            v___x_5274_ = (lean_unbox(v_defValue_5268_) as u8);
            return v___x_5274_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16___boxed(
    mut v_opts_5275_: *mut LeanObject,
    mut v_opt_5276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5277_: u8 = 0;
    let mut v_r_5278_: *mut LeanObject = core::ptr::null_mut();
    v_res_5277_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_5275_, v_opt_5276_);
    lean_dec_ref(v_opt_5276_);
    lean_dec_ref(v_opts_5275_);
    v_r_5278_ = lean_box((v_res_5277_) as usize);
    return v_r_5278_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    v___x_5282_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__1;
    v___x_5283_ = l_Lean_MessageData_ofFormat(v___x_5282_);
    return v___x_5283_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(
    mut v_msgData_5284_: *mut LeanObject,
    mut v_macroStack_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: u8 = 0;
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5309_: u8 = 0;
    let mut v_unused_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5288_ = lean_ctor_get(v___y_5286_, 2);
                v___x_5289_ = l_Lean_Elab_pp_macroStack;
                v___x_5290_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_options_5288_, v___x_5289_);
                if v___x_5290_ == 0 {
                    lean_dec(v_macroStack_5285_);
                    v___x_5291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5291_, 0, v_msgData_5284_);
                    return v___x_5291_;
                } else {
                    if lean_obj_tag(v_macroStack_5285_) == 0 {
                        v___x_5292_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5292_, 0, v_msgData_5284_);
                        return v___x_5292_;
                    } else {
                        v_head_5293_ = lean_ctor_get(v_macroStack_5285_, 0);
                        lean_inc(v_head_5293_);
                        v_after_5294_ = lean_ctor_get(v_head_5293_, 1);
                        v_isSharedCheck_5309_ = (!lean_is_exclusive(v_head_5293_)) as u8;
                        if v_isSharedCheck_5309_ == 0 {
                            v_unused_5310_ = lean_ctor_get(v_head_5293_, 0);
                            lean_dec(v_unused_5310_);
                            v___x_5296_ = v_head_5293_;
                            v_isShared_5297_ = v_isSharedCheck_5309_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_5294_);
                            lean_dec(v_head_5293_);
                            v___x_5296_ = lean_box(0);
                            v_isShared_5297_ = v_isSharedCheck_5309_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5298_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
                if v_isShared_5297_ == 0 {
                    lean_ctor_set_tag(v___x_5296_, 7);
                    lean_ctor_set(v___x_5296_, 1, v___x_5298_);
                    lean_ctor_set(v___x_5296_, 0, v_msgData_5284_);
                    v___x_5300_ = v___x_5296_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5308_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_msgData_5284_);
                    lean_ctor_set(v_reuseFailAlloc_5308_, 1, v___x_5298_);
                    v___x_5300_ = v_reuseFailAlloc_5308_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5301_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
                v___x_5302_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5302_, 0, v___x_5300_);
                lean_ctor_set(v___x_5302_, 1, v___x_5301_);
                v___x_5303_ = l_Lean_MessageData_ofSyntax(v_after_5294_);
                v___x_5304_ = l_Lean_indentD(v___x_5303_);
                v_msgData_5305_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_5305_, 0, v___x_5302_);
                lean_ctor_set(v_msgData_5305_, 1, v___x_5304_);
                v___x_5306_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_5305_, v_macroStack_5285_);
                v___x_5307_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5307_, 0, v___x_5306_);
                return v___x_5307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___boxed(
    mut v_msgData_5311_: *mut LeanObject,
    mut v_macroStack_5312_: *mut LeanObject,
    mut v___y_5313_: *mut LeanObject,
    mut v___y_5314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5315_: *mut LeanObject = core::ptr::null_mut();
    v_res_5315_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_5311_, v_macroStack_5312_, v___y_5313_);
    lean_dec_ref(v___y_5313_);
    return v_res_5315_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(
    mut v_msg_5316_: *mut LeanObject,
    mut v___y_5317_: *mut LeanObject,
    mut v___y_5318_: *mut LeanObject,
    mut v___y_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
    mut v___y_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_5324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_5327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5333_: u8 = 0;
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5324_ = lean_ctor_get(v___y_5321_, 5);
                v___x_5325_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v_msg_5316_, v___y_5319_, v___y_5320_, v___y_5321_, v___y_5322_);
                v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
                lean_inc(v_a_5326_);
                lean_dec_ref(v___x_5325_);
                v_macroStack_5327_ = lean_ctor_get(v___y_5317_, 1);
                v___x_5328_ = l_Lean_Elab_getBetterRef(v_ref_5324_, v_macroStack_5327_);
                lean_inc(v_macroStack_5327_);
                v___x_5329_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_a_5326_, v_macroStack_5327_, v___y_5321_);
                v_a_5330_ = lean_ctor_get(v___x_5329_, 0);
                v_isSharedCheck_5338_ = (!lean_is_exclusive(v___x_5329_)) as u8;
                if v_isSharedCheck_5338_ == 0 {
                    v___x_5332_ = v___x_5329_;
                    v_isShared_5333_ = v_isSharedCheck_5338_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_5330_);
                    lean_dec(v___x_5329_);
                    v___x_5332_ = lean_box(0);
                    v_isShared_5333_ = v_isSharedCheck_5338_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5334_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5334_, 0, v___x_5328_);
                lean_ctor_set(v___x_5334_, 1, v_a_5330_);
                if v_isShared_5333_ == 0 {
                    lean_ctor_set_tag(v___x_5332_, 1);
                    lean_ctor_set(v___x_5332_, 0, v___x_5334_);
                    v___x_5336_ = v___x_5332_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5337_, 0, v___x_5334_);
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
    mut v_msg_5339_: *mut LeanObject,
    mut v___y_5340_: *mut LeanObject,
    mut v___y_5341_: *mut LeanObject,
    mut v___y_5342_: *mut LeanObject,
    mut v___y_5343_: *mut LeanObject,
    mut v___y_5344_: *mut LeanObject,
    mut v___y_5345_: *mut LeanObject,
    mut v___y_5346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5347_: *mut LeanObject = core::ptr::null_mut();
    v_res_5347_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_5339_, v___y_5340_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_, v___y_5345_);
    lean_dec(v___y_5345_);
    lean_dec_ref(v___y_5344_);
    lean_dec(v___y_5343_);
    lean_dec_ref(v___y_5342_);
    lean_dec(v___y_5341_);
    lean_dec_ref(v___y_5340_);
    return v_res_5347_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(
    mut v_ref_5348_: *mut LeanObject,
    mut v_msg_5349_: *mut LeanObject,
    mut v___y_5350_: *mut LeanObject,
    mut v___y_5351_: *mut LeanObject,
    mut v___y_5352_: *mut LeanObject,
    mut v___y_5353_: *mut LeanObject,
    mut v___y_5354_: *mut LeanObject,
    mut v___y_5355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_5369_: u8 = 0;
    let mut v_cancelTk_x3f_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5371_: u8 = 0;
    let mut v_inheritedTraceOptions_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_5357_ = lean_ctor_get(v___y_5354_, 0);
    v_fileMap_5358_ = lean_ctor_get(v___y_5354_, 1);
    v_options_5359_ = lean_ctor_get(v___y_5354_, 2);
    v_currRecDepth_5360_ = lean_ctor_get(v___y_5354_, 3);
    v_maxRecDepth_5361_ = lean_ctor_get(v___y_5354_, 4);
    v_ref_5362_ = lean_ctor_get(v___y_5354_, 5);
    v_currNamespace_5363_ = lean_ctor_get(v___y_5354_, 6);
    v_openDecls_5364_ = lean_ctor_get(v___y_5354_, 7);
    v_initHeartbeats_5365_ = lean_ctor_get(v___y_5354_, 8);
    v_maxHeartbeats_5366_ = lean_ctor_get(v___y_5354_, 9);
    v_quotContext_5367_ = lean_ctor_get(v___y_5354_, 10);
    v_currMacroScope_5368_ = lean_ctor_get(v___y_5354_, 11);
    v_diag_5369_ = lean_ctor_get_uint8(
        v___y_5354_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_5370_ = lean_ctor_get(v___y_5354_, 12);
    v_suppressElabErrors_5371_ = lean_ctor_get_uint8(
        v___y_5354_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_5372_ = lean_ctor_get(v___y_5354_, 13);
    v_ref_5373_ = l_Lean_replaceRef(v_ref_5348_, v_ref_5362_);
    lean_inc_ref(v_inheritedTraceOptions_5372_);
    lean_inc(v_cancelTk_x3f_5370_);
    lean_inc(v_currMacroScope_5368_);
    lean_inc(v_quotContext_5367_);
    lean_inc(v_maxHeartbeats_5366_);
    lean_inc(v_initHeartbeats_5365_);
    lean_inc(v_openDecls_5364_);
    lean_inc(v_currNamespace_5363_);
    lean_inc(v_maxRecDepth_5361_);
    lean_inc(v_currRecDepth_5360_);
    lean_inc_ref(v_options_5359_);
    lean_inc_ref(v_fileMap_5358_);
    lean_inc_ref(v_fileName_5357_);
    v___x_5374_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_5374_, 0, v_fileName_5357_);
    lean_ctor_set(v___x_5374_, 1, v_fileMap_5358_);
    lean_ctor_set(v___x_5374_, 2, v_options_5359_);
    lean_ctor_set(v___x_5374_, 3, v_currRecDepth_5360_);
    lean_ctor_set(v___x_5374_, 4, v_maxRecDepth_5361_);
    lean_ctor_set(v___x_5374_, 5, v_ref_5373_);
    lean_ctor_set(v___x_5374_, 6, v_currNamespace_5363_);
    lean_ctor_set(v___x_5374_, 7, v_openDecls_5364_);
    lean_ctor_set(v___x_5374_, 8, v_initHeartbeats_5365_);
    lean_ctor_set(v___x_5374_, 9, v_maxHeartbeats_5366_);
    lean_ctor_set(v___x_5374_, 10, v_quotContext_5367_);
    lean_ctor_set(v___x_5374_, 11, v_currMacroScope_5368_);
    lean_ctor_set(v___x_5374_, 12, v_cancelTk_x3f_5370_);
    lean_ctor_set(v___x_5374_, 13, v_inheritedTraceOptions_5372_);
    lean_ctor_set_uint8(
        v___x_5374_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_5369_,
    );
    lean_ctor_set_uint8(
        v___x_5374_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_5371_,
    );
    v___x_5375_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_5349_, v___y_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___x_5374_, v___y_5355_);
    lean_dec_ref_known(v___x_5374_, 14);
    return v___x_5375_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg___boxed(
    mut v_ref_5376_: *mut LeanObject,
    mut v_msg_5377_: *mut LeanObject,
    mut v___y_5378_: *mut LeanObject,
    mut v___y_5379_: *mut LeanObject,
    mut v___y_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
    mut v___y_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5385_: *mut LeanObject = core::ptr::null_mut();
    v_res_5385_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_5376_, v_msg_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_, v___y_5383_);
    lean_dec(v___y_5383_);
    lean_dec_ref(v___y_5382_);
    lean_dec(v___y_5381_);
    lean_dec_ref(v___y_5380_);
    lean_dec(v___y_5379_);
    lean_dec_ref(v___y_5378_);
    lean_dec(v_ref_5376_);
    return v_res_5385_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(
    mut v_x_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
    mut v___y_5389_: *mut LeanObject,
    mut v___y_5390_: *mut LeanObject,
    mut v___y_5391_: *mut LeanObject,
    mut v___y_5392_: *mut LeanObject,
    mut v___y_5393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_5404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_methods_5412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroScope_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_5420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5435_: u8 = 0;
    let mut v___x_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5443_: u8 = 0;
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5447_: u8 = 0;
    let mut v_unused_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5452_: u8 = 0;
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5456_: u8 = 0;
    let mut v_reuseFailAlloc_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5458_: u8 = 0;
    let mut v_unused_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut v_a_5468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: u8 = 0;
    let mut v___x_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5395_ = lean_st_ref_get(v___y_5393_);
                v_env_5396_ = lean_ctor_get(v___x_5395_, 0);
                lean_inc_ref_n(v_env_5396_, 4);
                lean_dec(v___x_5395_);
                v_options_5397_ = lean_ctor_get(v___y_5392_, 2);
                v_currRecDepth_5398_ = lean_ctor_get(v___y_5392_, 3);
                v_maxRecDepth_5399_ = lean_ctor_get(v___y_5392_, 4);
                v_ref_5400_ = lean_ctor_get(v___y_5392_, 5);
                v_currNamespace_5401_ = lean_ctor_get(v___y_5392_, 6);
                v_openDecls_5402_ = lean_ctor_get(v___y_5392_, 7);
                v_quotContext_5403_ = lean_ctor_get(v___y_5392_, 10);
                v_currMacroScope_5404_ = lean_ctor_get(v___y_5392_, 11);
                v___x_5405_ = lean_st_ref_get(v___y_5393_);
                v_nextMacroScope_5406_ = lean_ctor_get(v___x_5405_, 1);
                lean_inc(v_nextMacroScope_5406_);
                lean_dec(v___x_5405_);
                v___f_5407_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                lean_closure_set(v___f_5407_, 0, v_env_5396_);
                v___f_5408_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                lean_closure_set(v___f_5408_, 0, v_env_5396_);
                lean_inc_n(v_openDecls_5402_, 2);
                lean_inc_n(v_currNamespace_5401_, 3);
                v___f_5409_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                lean_closure_set(v___f_5409_, 0, v_env_5396_);
                lean_closure_set(v___f_5409_, 1, v_currNamespace_5401_);
                lean_closure_set(v___f_5409_, 2, v_openDecls_5402_);
                v___f_5410_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                lean_closure_set(v___f_5410_, 0, v_currNamespace_5401_);
                lean_inc_ref(v_options_5397_);
                v___f_5411_ = lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                lean_closure_set(v___f_5411_, 0, v_env_5396_);
                lean_closure_set(v___f_5411_, 1, v_options_5397_);
                lean_closure_set(v___f_5411_, 2, v_currNamespace_5401_);
                lean_closure_set(v___f_5411_, 3, v_openDecls_5402_);
                v_methods_5412_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v_methods_5412_, 0, v___f_5407_);
                lean_ctor_set(v_methods_5412_, 1, v___f_5410_);
                lean_ctor_set(v_methods_5412_, 2, v___f_5408_);
                lean_ctor_set(v_methods_5412_, 3, v___f_5409_);
                lean_ctor_set(v_methods_5412_, 4, v___f_5411_);
                lean_inc(v_ref_5400_);
                lean_inc(v_maxRecDepth_5399_);
                lean_inc(v_currRecDepth_5398_);
                lean_inc(v_currMacroScope_5404_);
                lean_inc(v_quotContext_5403_);
                v___x_5413_ = lean_alloc_ctor(0, 6, (0) as u32);
                lean_ctor_set(v___x_5413_, 0, v_methods_5412_);
                lean_ctor_set(v___x_5413_, 1, v_quotContext_5403_);
                lean_ctor_set(v___x_5413_, 2, v_currMacroScope_5404_);
                lean_ctor_set(v___x_5413_, 3, v_currRecDepth_5398_);
                lean_ctor_set(v___x_5413_, 4, v_maxRecDepth_5399_);
                lean_ctor_set(v___x_5413_, 5, v_ref_5400_);
                v___x_5414_ = lean_box(0);
                v___x_5415_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_5415_, 0, v_nextMacroScope_5406_);
                lean_ctor_set(v___x_5415_, 1, v___x_5414_);
                lean_ctor_set(v___x_5415_, 2, v___x_5414_);
                v___x_5416_ = lean_apply_2(v_x_5387_, v___x_5413_, v___x_5415_);
                if lean_obj_tag(v___x_5416_) == 0 {
                    v_a_5417_ = lean_ctor_get(v___x_5416_, 1);
                    lean_inc(v_a_5417_);
                    v_a_5418_ = lean_ctor_get(v___x_5416_, 0);
                    lean_inc(v_a_5418_);
                    lean_dec_ref_known(v___x_5416_, 2);
                    v_macroScope_5419_ = lean_ctor_get(v_a_5417_, 0);
                    lean_inc(v_macroScope_5419_);
                    v_traceMsgs_5420_ = lean_ctor_get(v_a_5417_, 1);
                    lean_inc(v_traceMsgs_5420_);
                    v_expandedMacroDecls_5421_ = lean_ctor_get(v_a_5417_, 2);
                    lean_inc(v_expandedMacroDecls_5421_);
                    lean_dec(v_a_5417_);
                    v___x_5422_ = lean_box(0);
                    v___x_5423_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_expandedMacroDecls_5421_, v___x_5422_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
                    lean_dec(v_expandedMacroDecls_5421_);
                    if lean_obj_tag(v___x_5423_) == 0 {
                        lean_dec_ref_known(v___x_5423_, 1);
                        v___x_5424_ = lean_st_ref_take(v___y_5393_);
                        v_env_5425_ = lean_ctor_get(v___x_5424_, 0);
                        v_ngen_5426_ = lean_ctor_get(v___x_5424_, 2);
                        v_auxDeclNGen_5427_ = lean_ctor_get(v___x_5424_, 3);
                        v_traceState_5428_ = lean_ctor_get(v___x_5424_, 4);
                        v_cache_5429_ = lean_ctor_get(v___x_5424_, 5);
                        v_messages_5430_ = lean_ctor_get(v___x_5424_, 6);
                        v_infoState_5431_ = lean_ctor_get(v___x_5424_, 7);
                        v_snapshotTasks_5432_ = lean_ctor_get(v___x_5424_, 8);
                        v_isSharedCheck_5458_ = (!lean_is_exclusive(v___x_5424_)) as u8;
                        if v_isSharedCheck_5458_ == 0 {
                            v_unused_5459_ = lean_ctor_get(v___x_5424_, 1);
                            lean_dec(v_unused_5459_);
                            v___x_5434_ = v___x_5424_;
                            v_isShared_5435_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snapshotTasks_5432_);
                            lean_inc(v_infoState_5431_);
                            lean_inc(v_messages_5430_);
                            lean_inc(v_cache_5429_);
                            lean_inc(v_traceState_5428_);
                            lean_inc(v_auxDeclNGen_5427_);
                            lean_inc(v_ngen_5426_);
                            lean_inc(v_env_5425_);
                            lean_dec(v___x_5424_);
                            v___x_5434_ = lean_box(0);
                            v_isShared_5435_ = v_isSharedCheck_5458_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_traceMsgs_5420_);
                        lean_dec(v_macroScope_5419_);
                        lean_dec(v_a_5418_);
                        v_a_5460_ = lean_ctor_get(v___x_5423_, 0);
                        v_isSharedCheck_5467_ = (!lean_is_exclusive(v___x_5423_)) as u8;
                        if v_isSharedCheck_5467_ == 0 {
                            v___x_5462_ = v___x_5423_;
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_5460_);
                            lean_dec(v___x_5423_);
                            v___x_5462_ = lean_box(0);
                            v_isShared_5463_ = v_isSharedCheck_5467_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_5468_ = lean_ctor_get(v___x_5416_, 0);
                    lean_inc(v_a_5468_);
                    lean_dec_ref_known(v___x_5416_, 2);
                    if lean_obj_tag(v_a_5468_) == 0 {
                        v_a_5469_ = lean_ctor_get(v_a_5468_, 0);
                        lean_inc(v_a_5469_);
                        v_a_5470_ = lean_ctor_get(v_a_5468_, 1);
                        lean_inc_ref(v_a_5470_);
                        lean_dec_ref_known(v_a_5468_, 2);
                        v___x_5471_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg___closed__0;
                        v___x_5472_ = lean_string_dec_eq(v_a_5470_, v___x_5471_);
                        if v___x_5472_ == 0 {
                            v___x_5473_ = lean_alloc_ctor(3, 1, (0) as u32);
                            lean_ctor_set(v___x_5473_, 0, v_a_5470_);
                            v___x_5474_ = l_Lean_MessageData_ofFormat(v___x_5473_);
                            v___x_5475_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_a_5469_, v___x_5474_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
                            lean_dec(v_a_5469_);
                            return v___x_5475_;
                        } else {
                            lean_dec_ref(v_a_5470_);
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
                    lean_ctor_set(v___x_5434_, 1, v_macroScope_5419_);
                    v___x_5437_ = v___x_5434_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_env_5425_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_macroScope_5419_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_ngen_5426_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_auxDeclNGen_5427_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 4, v_traceState_5428_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 5, v_cache_5429_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 6, v_messages_5430_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 7, v_infoState_5431_);
                    lean_ctor_set(v_reuseFailAlloc_5457_, 8, v_snapshotTasks_5432_);
                    v___x_5437_ = v_reuseFailAlloc_5457_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5438_ = lean_st_ref_set(v___y_5393_, v___x_5437_);
                v___x_5439_ = l_List_reverse___redArg(v_traceMsgs_5420_);
                v___x_5440_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__4(v___x_5439_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
                if lean_obj_tag(v___x_5440_) == 0 {
                    v_isSharedCheck_5447_ = (!lean_is_exclusive(v___x_5440_)) as u8;
                    if v_isSharedCheck_5447_ == 0 {
                        v_unused_5448_ = lean_ctor_get(v___x_5440_, 0);
                        lean_dec(v_unused_5448_);
                        v___x_5442_ = v___x_5440_;
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_5440_);
                        v___x_5442_ = lean_box(0);
                        v_isShared_5443_ = v_isSharedCheck_5447_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5418_);
                    v_a_5449_ = lean_ctor_get(v___x_5440_, 0);
                    v_isSharedCheck_5456_ = (!lean_is_exclusive(v___x_5440_)) as u8;
                    if v_isSharedCheck_5456_ == 0 {
                        v___x_5451_ = v___x_5440_;
                        v_isShared_5452_ = v_isSharedCheck_5456_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_5449_);
                        lean_dec(v___x_5440_);
                        v___x_5451_ = lean_box(0);
                        v_isShared_5452_ = v_isSharedCheck_5456_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5443_ == 0 {
                    lean_ctor_set(v___x_5442_, 0, v_a_5418_);
                    v___x_5445_ = v___x_5442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5418_);
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
                    v_reuseFailAlloc_5455_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_a_5449_);
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
                    v_reuseFailAlloc_5466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
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
    mut v_x_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5486_: *mut LeanObject = core::ptr::null_mut();
    v_res_5486_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_5478_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_);
    lean_dec(v___y_5484_);
    lean_dec_ref(v___y_5483_);
    lean_dec(v___y_5482_);
    lean_dec_ref(v___y_5481_);
    lean_dec(v___y_5480_);
    lean_dec_ref(v___y_5479_);
    return v_res_5486_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(
    mut v_t_5487_: *mut LeanObject,
    mut v___y_5488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_5492_: u8 = 0;
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5507_: u8 = 0;
    let mut v_enabled_5508_: u8 = 0;
    let mut v_assignment_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lazyAssignment_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trees_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5514_: u8 = 0;
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5525_: u8 = 0;
    let mut v_isSharedCheck_5526_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5490_ = lean_st_ref_get(v___y_5488_);
                v_infoState_5491_ = lean_ctor_get(v___x_5490_, 7);
                lean_inc_ref(v_infoState_5491_);
                lean_dec(v___x_5490_);
                v_enabled_5492_ = lean_ctor_get_uint8(
                    v_infoState_5491_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                lean_dec_ref(v_infoState_5491_);
                if v_enabled_5492_ == 0 {
                    lean_dec_ref(v_t_5487_);
                    v___x_5493_ = lean_box(0);
                    v___x_5494_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5494_, 0, v___x_5493_);
                    return v___x_5494_;
                } else {
                    v___x_5495_ = lean_st_ref_take(v___y_5488_);
                    v_infoState_5496_ = lean_ctor_get(v___x_5495_, 7);
                    v_env_5497_ = lean_ctor_get(v___x_5495_, 0);
                    v_nextMacroScope_5498_ = lean_ctor_get(v___x_5495_, 1);
                    v_ngen_5499_ = lean_ctor_get(v___x_5495_, 2);
                    v_auxDeclNGen_5500_ = lean_ctor_get(v___x_5495_, 3);
                    v_traceState_5501_ = lean_ctor_get(v___x_5495_, 4);
                    v_cache_5502_ = lean_ctor_get(v___x_5495_, 5);
                    v_messages_5503_ = lean_ctor_get(v___x_5495_, 6);
                    v_snapshotTasks_5504_ = lean_ctor_get(v___x_5495_, 8);
                    v_isSharedCheck_5526_ = (!lean_is_exclusive(v___x_5495_)) as u8;
                    if v_isSharedCheck_5526_ == 0 {
                        v___x_5506_ = v___x_5495_;
                        v_isShared_5507_ = v_isSharedCheck_5526_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snapshotTasks_5504_);
                        lean_inc(v_infoState_5496_);
                        lean_inc(v_messages_5503_);
                        lean_inc(v_cache_5502_);
                        lean_inc(v_traceState_5501_);
                        lean_inc(v_auxDeclNGen_5500_);
                        lean_inc(v_ngen_5499_);
                        lean_inc(v_nextMacroScope_5498_);
                        lean_inc(v_env_5497_);
                        lean_dec(v___x_5495_);
                        v___x_5506_ = lean_box(0);
                        v_isShared_5507_ = v_isSharedCheck_5526_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_enabled_5508_ = lean_ctor_get_uint8(
                    v_infoState_5496_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_assignment_5509_ = lean_ctor_get(v_infoState_5496_, 0);
                v_lazyAssignment_5510_ = lean_ctor_get(v_infoState_5496_, 1);
                v_trees_5511_ = lean_ctor_get(v_infoState_5496_, 2);
                v_isSharedCheck_5525_ = (!lean_is_exclusive(v_infoState_5496_)) as u8;
                if v_isSharedCheck_5525_ == 0 {
                    v___x_5513_ = v_infoState_5496_;
                    v_isShared_5514_ = v_isSharedCheck_5525_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_trees_5511_);
                    lean_inc(v_lazyAssignment_5510_);
                    lean_inc(v_assignment_5509_);
                    lean_dec(v_infoState_5496_);
                    v___x_5513_ = lean_box(0);
                    v_isShared_5514_ = v_isSharedCheck_5525_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5515_ = l_Lean_PersistentArray_push___redArg(v_trees_5511_, v_t_5487_);
                if v_isShared_5514_ == 0 {
                    lean_ctor_set(v___x_5513_, 2, v___x_5515_);
                    v___x_5517_ = v___x_5513_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_assignment_5509_);
                    lean_ctor_set(v_reuseFailAlloc_5524_, 1, v_lazyAssignment_5510_);
                    lean_ctor_set(v_reuseFailAlloc_5524_, 2, v___x_5515_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5524_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_enabled_5508_,
                    );
                    v___x_5517_ = v_reuseFailAlloc_5524_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5507_ == 0 {
                    lean_ctor_set(v___x_5506_, 7, v___x_5517_);
                    v___x_5519_ = v___x_5506_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 0, v_env_5497_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_nextMacroScope_5498_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_ngen_5499_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_auxDeclNGen_5500_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_traceState_5501_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 5, v_cache_5502_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 6, v_messages_5503_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 7, v___x_5517_);
                    lean_ctor_set(v_reuseFailAlloc_5523_, 8, v_snapshotTasks_5504_);
                    v___x_5519_ = v_reuseFailAlloc_5523_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5520_ = lean_st_ref_set(v___y_5488_, v___x_5519_);
                v___x_5521_ = lean_box(0);
                v___x_5522_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                return v___x_5522_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg___boxed(
    mut v_t_5527_: *mut LeanObject,
    mut v___y_5528_: *mut LeanObject,
    mut v___y_5529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5530_: *mut LeanObject = core::ptr::null_mut();
    v_res_5530_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_5527_, v___y_5528_);
    lean_dec(v___y_5528_);
    return v_res_5530_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    v___x_5531_ = lean_unsigned_to_nat(32);
    v___x_5532_ = lean_mk_empty_array_with_capacity(v___x_5531_);
    v___x_5533_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5533_, 0, v___x_5532_);
    return v___x_5533_;
}
pub unsafe fn _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_5534_: usize = 0;
    let mut v___x_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    v___x_5534_ = 5usize;
    v___x_5535_ = lean_unsigned_to_nat(0);
    v___x_5536_ = lean_unsigned_to_nat(32);
    v___x_5537_ = lean_mk_empty_array_with_capacity(v___x_5536_);
    v___x_5538_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__0);
    v___x_5539_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_5539_, 0, v___x_5538_);
    lean_ctor_set(v___x_5539_, 1, v___x_5537_);
    lean_ctor_set(v___x_5539_, 2, v___x_5535_);
    lean_ctor_set(v___x_5539_, 3, v___x_5535_);
    lean_ctor_set_usize(v___x_5539_, 4, v___x_5534_);
    return v___x_5539_;
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(
    mut v_t_5540_: *mut LeanObject,
    mut v___y_5541_: *mut LeanObject,
    mut v___y_5542_: *mut LeanObject,
    mut v___y_5543_: *mut LeanObject,
    mut v___y_5544_: *mut LeanObject,
    mut v___y_5545_: *mut LeanObject,
    mut v___y_5546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_enabled_5550_: u8 = 0;
    v___x_5548_ = lean_st_ref_get(v___y_5546_);
    v_infoState_5549_ = lean_ctor_get(v___x_5548_, 7);
    lean_inc_ref(v_infoState_5549_);
    lean_dec(v___x_5548_);
    v_enabled_5550_ = lean_ctor_get_uint8(
        v_infoState_5549_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    lean_dec_ref(v_infoState_5549_);
    if v_enabled_5550_ == 0 {
        let mut v___x_5551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5552_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_t_5540_);
        v___x_5551_ = lean_box(0);
        v___x_5552_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_5552_, 0, v___x_5551_);
        return v___x_5552_;
    } else {
        let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
        v___x_5553_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1_once), _init_l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___closed__1);
        v___x_5554_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_5554_, 0, v_t_5540_);
        lean_ctor_set(v___x_5554_, 1, v___x_5553_);
        v___x_5555_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v___x_5554_, v___y_5546_);
        return v___x_5555_;
    }
}
pub unsafe fn l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2___boxed(
    mut v_t_5556_: *mut LeanObject,
    mut v___y_5557_: *mut LeanObject,
    mut v___y_5558_: *mut LeanObject,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5564_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5562_);
    lean_dec_ref(v___y_5561_);
    lean_dec(v___y_5560_);
    lean_dec_ref(v___y_5559_);
    lean_dec(v___y_5558_);
    lean_dec_ref(v___y_5557_);
    return v_res_5564_;
}
pub unsafe fn l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(
    mut v_info_5565_: *mut LeanObject,
    mut v___y_5566_: *mut LeanObject,
    mut v___y_5567_: *mut LeanObject,
    mut v___y_5568_: *mut LeanObject,
    mut v___y_5569_: *mut LeanObject,
    mut v___y_5570_: *mut LeanObject,
    mut v___y_5571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    v___x_5573_ = lean_alloc_ctor(8, 1, (0) as u32);
    lean_ctor_set(v___x_5573_, 0, v_info_5565_);
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
    mut v_info_5575_: *mut LeanObject,
    mut v___y_5576_: *mut LeanObject,
    mut v___y_5577_: *mut LeanObject,
    mut v___y_5578_: *mut LeanObject,
    mut v___y_5579_: *mut LeanObject,
    mut v___y_5580_: *mut LeanObject,
    mut v___y_5581_: *mut LeanObject,
    mut v___y_5582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5583_: *mut LeanObject = core::ptr::null_mut();
    v_res_5583_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v_info_5575_, v___y_5576_, v___y_5577_, v___y_5578_, v___y_5579_, v___y_5580_, v___y_5581_);
    lean_dec(v___y_5581_);
    lean_dec_ref(v___y_5580_);
    lean_dec(v___y_5579_);
    lean_dec_ref(v___y_5578_);
    lean_dec(v___y_5577_);
    lean_dec_ref(v___y_5576_);
    return v_res_5583_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(
    mut v___y_5591_: u8,
    mut v_suppressElabErrors_5592_: u8,
    mut v_x_5593_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_5593_) == 1 {
        let mut v_pre_5594_: *mut LeanObject = core::ptr::null_mut();
        v_pre_5594_ = lean_ctor_get(v_x_5593_, 0);
        match lean_obj_tag(v_pre_5594_) {
            1 => {
                let mut v_pre_5595_: *mut LeanObject = core::ptr::null_mut();
                v_pre_5595_ = lean_ctor_get(v_pre_5594_, 0);
                match lean_obj_tag(v_pre_5595_) {
                    0 => {
                        let mut v_str_5596_: *mut LeanObject = core::ptr::null_mut();
                        let mut v_str_5597_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5598_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_5599_: u8 = 0;
                        v_str_5596_ = lean_ctor_get(v_x_5593_, 1);
                        v_str_5597_ = lean_ctor_get(v_pre_5594_, 1);
                        v___x_5598_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__0;
                        v___x_5599_ = lean_string_dec_eq(v_str_5597_, v___x_5598_);
                        if v___x_5599_ == 0 {
                            let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_5601_: u8 = 0;
                            v___x_5600_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__1;
                            v___x_5601_ = lean_string_dec_eq(v_str_5597_, v___x_5600_);
                            if v___x_5601_ == 0 {
                                return v___y_5591_;
                            } else {
                                let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
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
                            let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
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
                        let mut v_pre_5606_: *mut LeanObject = core::ptr::null_mut();
                        v_pre_5606_ = lean_ctor_get(v_pre_5595_, 0);
                        if lean_obj_tag(v_pre_5606_) == 0 {
                            let mut v_str_5607_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_5608_: *mut LeanObject = core::ptr::null_mut();
                            let mut v_str_5609_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
                            let mut v___x_5611_: u8 = 0;
                            v_str_5607_ = lean_ctor_get(v_x_5593_, 1);
                            v_str_5608_ = lean_ctor_get(v_pre_5594_, 1);
                            v_str_5609_ = lean_ctor_get(v_pre_5595_, 1);
                            v___x_5610_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__4;
                            v___x_5611_ = lean_string_dec_eq(v_str_5609_, v___x_5610_);
                            if v___x_5611_ == 0 {
                                return v___y_5591_;
                            } else {
                                let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
                                let mut v___x_5613_: u8 = 0;
                                v___x_5612_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___closed__5;
                                v___x_5613_ = lean_string_dec_eq(v_str_5608_, v___x_5612_);
                                if v___x_5613_ == 0 {
                                    return v___y_5591_;
                                } else {
                                    let mut v___x_5614_: *mut LeanObject = core::ptr::null_mut();
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
                let mut v_str_5616_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_5618_: u8 = 0;
                v_str_5616_ = lean_ctor_get(v_x_5593_, 1);
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
    mut v___y_5619_: *mut LeanObject,
    mut v_suppressElabErrors_5620_: *mut LeanObject,
    mut v_x_5621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_21547__boxed_5622_: u8 = 0;
    let mut v_suppressElabErrors_boxed_5623_: u8 = 0;
    let mut v_res_5624_: u8 = 0;
    let mut v_r_5625_: *mut LeanObject = core::ptr::null_mut();
    v___y_21547__boxed_5622_ = (lean_unbox(v___y_5619_) as u8);
    v_suppressElabErrors_boxed_5623_ = (lean_unbox(v_suppressElabErrors_5620_) as u8);
    v_res_5624_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0(v___y_21547__boxed_5622_, v_suppressElabErrors_boxed_5623_, v_x_5621_);
    lean_dec(v_x_5621_);
    v_r_5625_ = lean_box((v_res_5624_) as usize);
    return v_r_5625_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(
    mut v_ref_5626_: *mut LeanObject,
    mut v_msgData_5627_: *mut LeanObject,
    mut v_severity_5628_: u8,
    mut v_isSilent_5629_: u8,
    mut v___y_5630_: *mut LeanObject,
    mut v___y_5631_: *mut LeanObject,
    mut v___y_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5641_: u8 = 0;
    let mut v___y_5642_: u8 = 0;
    let mut v___y_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_5646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5659_: u8 = 0;
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5670_: u8 = 0;
    let mut v___y_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5676_: u8 = 0;
    let mut v___y_5677_: u8 = 0;
    let mut v___y_5678_: u8 = 0;
    let mut v___y_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5685_: u8 = 0;
    let mut v___x_5686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5690_: u8 = 0;
    let mut v___x_5691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5695_: u8 = 0;
    let mut v___y_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5701_: u8 = 0;
    let mut v___y_5702_: u8 = 0;
    let mut v___y_5703_: u8 = 0;
    let mut v___y_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5712_: u8 = 0;
    let mut v___y_5713_: u8 = 0;
    let mut v___y_5714_: u8 = 0;
    let mut v_ref_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5719_: u8 = 0;
    let mut v___y_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5724_: u8 = 0;
    let mut v___y_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5726_: u8 = 0;
    let mut v___y_5727_: u8 = 0;
    let mut v___y_5729_: u8 = 0;
    let mut v_fileName_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_5734_: u8 = 0;
    let mut v___x_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    let mut v___x_5739_: u8 = 0;
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: *mut LeanObject = core::ptr::null_mut();
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
                    lean_inc_ref(v_msgData_5627_);
                    v___x_5745_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_5627_);
                    v___y_5729_ = v___x_5745_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_5645_ = lean_st_ref_take(v___y_5644_);
                v_currNamespace_5646_ = lean_ctor_get(v___y_5643_, 6);
                v_openDecls_5647_ = lean_ctor_get(v___y_5643_, 7);
                v_env_5648_ = lean_ctor_get(v___x_5645_, 0);
                v_nextMacroScope_5649_ = lean_ctor_get(v___x_5645_, 1);
                v_ngen_5650_ = lean_ctor_get(v___x_5645_, 2);
                v_auxDeclNGen_5651_ = lean_ctor_get(v___x_5645_, 3);
                v_traceState_5652_ = lean_ctor_get(v___x_5645_, 4);
                v_cache_5653_ = lean_ctor_get(v___x_5645_, 5);
                v_messages_5654_ = lean_ctor_get(v___x_5645_, 6);
                v_infoState_5655_ = lean_ctor_get(v___x_5645_, 7);
                v_snapshotTasks_5656_ = lean_ctor_get(v___x_5645_, 8);
                v_isSharedCheck_5670_ = (!lean_is_exclusive(v___x_5645_)) as u8;
                if v_isSharedCheck_5670_ == 0 {
                    v___x_5658_ = v___x_5645_;
                    v_isShared_5659_ = v_isSharedCheck_5670_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_5656_);
                    lean_inc(v_infoState_5655_);
                    lean_inc(v_messages_5654_);
                    lean_inc(v_cache_5653_);
                    lean_inc(v_traceState_5652_);
                    lean_inc(v_auxDeclNGen_5651_);
                    lean_inc(v_ngen_5650_);
                    lean_inc(v_nextMacroScope_5649_);
                    lean_inc(v_env_5648_);
                    lean_dec(v___x_5645_);
                    v___x_5658_ = lean_box(0);
                    v_isShared_5659_ = v_isSharedCheck_5670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_openDecls_5647_);
                lean_inc(v_currNamespace_5646_);
                v___x_5660_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5660_, 0, v_currNamespace_5646_);
                lean_ctor_set(v___x_5660_, 1, v_openDecls_5647_);
                v___x_5661_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5661_, 0, v___x_5660_);
                lean_ctor_set(v___x_5661_, 1, v___y_5638_);
                lean_inc_ref(v___y_5639_);
                lean_inc_ref(v___y_5637_);
                v___x_5662_ = lean_alloc_ctor(0, 5, (3) as u32);
                lean_ctor_set(v___x_5662_, 0, v___y_5637_);
                lean_ctor_set(v___x_5662_, 1, v___y_5640_);
                lean_ctor_set(v___x_5662_, 2, v___y_5636_);
                lean_ctor_set(v___x_5662_, 3, v___y_5639_);
                lean_ctor_set(v___x_5662_, 4, v___x_5661_);
                lean_ctor_set_uint8(
                    v___x_5662_,
                    (core::mem::size_of::<*mut LeanObject>() * 5) as u32,
                    v___y_5642_,
                );
                lean_ctor_set_uint8(
                    v___x_5662_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 1) as u32,
                    v___y_5641_,
                );
                lean_ctor_set_uint8(
                    v___x_5662_,
                    (core::mem::size_of::<*mut LeanObject>() * 5 + 2) as u32,
                    v_isSilent_5629_,
                );
                v___x_5663_ = l_Lean_MessageLog_add(v___x_5662_, v_messages_5654_);
                if v_isShared_5659_ == 0 {
                    lean_ctor_set(v___x_5658_, 6, v___x_5663_);
                    v___x_5665_ = v___x_5658_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5669_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 0, v_env_5648_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 1, v_nextMacroScope_5649_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 2, v_ngen_5650_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 3, v_auxDeclNGen_5651_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 4, v_traceState_5652_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 5, v_cache_5653_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 6, v___x_5663_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 7, v_infoState_5655_);
                    lean_ctor_set(v_reuseFailAlloc_5669_, 8, v_snapshotTasks_5656_);
                    v___x_5665_ = v_reuseFailAlloc_5669_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5666_ = lean_st_ref_set(v___y_5644_, v___x_5665_);
                v___x_5667_ = lean_box(0);
                v___x_5668_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5668_, 0, v___x_5667_);
                return v___x_5668_;
            }
            4 => {
                v___x_5680_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_5627_,
                    );
                v___x_5681_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__18(v___x_5680_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_);
                v_a_5682_ = lean_ctor_get(v___x_5681_, 0);
                v_isSharedCheck_5695_ = (!lean_is_exclusive(v___x_5681_)) as u8;
                if v_isSharedCheck_5695_ == 0 {
                    v___x_5684_ = v___x_5681_;
                    v_isShared_5685_ = v_isSharedCheck_5695_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_a_5682_);
                    lean_dec(v___x_5681_);
                    v___x_5684_ = lean_box(0);
                    v_isShared_5685_ = v_isSharedCheck_5695_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                lean_inc_ref_n(v___y_5673_, 2);
                v___x_5686_ = l_Lean_FileMap_toPosition(v___y_5673_, v___y_5674_);
                lean_dec(v___y_5674_);
                v___x_5687_ = l_Lean_FileMap_toPosition(v___y_5673_, v___y_5679_);
                lean_dec(v___y_5679_);
                v___x_5688_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5688_, 0, v___x_5687_);
                v___x_5689_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                if v___y_5676_ == 0 {
                    lean_del_object(v___x_5684_);
                    lean_dec_ref(v___y_5672_);
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
                    lean_inc(v_a_5682_);
                    v___x_5690_ = l_Lean_MessageData_hasTag(v___y_5672_, v_a_5682_);
                    if v___x_5690_ == 0 {
                        lean_dec_ref_known(v___x_5688_, 1);
                        lean_dec_ref(v___x_5686_);
                        lean_dec(v_a_5682_);
                        v___x_5691_ = lean_box(0);
                        if v_isShared_5685_ == 0 {
                            lean_ctor_set(v___x_5684_, 0, v___x_5691_);
                            v___x_5693_ = v___x_5684_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5694_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5694_, 0, v___x_5691_);
                            v___x_5693_ = v_reuseFailAlloc_5694_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5684_);
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
                lean_dec(v___y_5698_);
                if lean_obj_tag(v___x_5705_) == 0 {
                    lean_inc(v___y_5704_);
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
                    v_val_5706_ = lean_ctor_get(v___x_5705_, 0);
                    lean_inc(v_val_5706_);
                    lean_dec_ref_known(v___x_5705_, 1);
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
                if lean_obj_tag(v___x_5716_) == 0 {
                    v___x_5717_ = lean_unsigned_to_nat(0);
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
                    v_val_5718_ = lean_ctor_get(v___x_5716_, 0);
                    lean_inc(v_val_5718_);
                    lean_dec_ref_known(v___x_5716_, 1);
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
                    v_fileName_5730_ = lean_ctor_get(v___y_5632_, 0);
                    v_fileMap_5731_ = lean_ctor_get(v___y_5632_, 1);
                    v_options_5732_ = lean_ctor_get(v___y_5632_, 2);
                    v_ref_5733_ = lean_ctor_get(v___y_5632_, 5);
                    v_suppressElabErrors_5734_ = lean_ctor_get_uint8(
                        v___y_5632_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_5735_ = lean_box((v___y_5729_) as usize);
                    v___x_5736_ = lean_box((v_suppressElabErrors_5734_) as usize);
                    v___f_5737_ = lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_5737_, 0, v___x_5735_);
                    lean_closure_set(v___f_5737_, 1, v___x_5736_);
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
                    lean_dec_ref(v_msgData_5627_);
                    v___x_5742_ = lean_box(0);
                    v___x_5743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5743_, 0, v___x_5742_);
                    return v___x_5743_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg___boxed(
    mut v_ref_5746_: *mut LeanObject,
    mut v_msgData_5747_: *mut LeanObject,
    mut v_severity_5748_: *mut LeanObject,
    mut v_isSilent_5749_: *mut LeanObject,
    mut v___y_5750_: *mut LeanObject,
    mut v___y_5751_: *mut LeanObject,
    mut v___y_5752_: *mut LeanObject,
    mut v___y_5753_: *mut LeanObject,
    mut v___y_5754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_5755_: u8 = 0;
    let mut v_isSilent_boxed_5756_: u8 = 0;
    let mut v_res_5757_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_5755_ = (lean_unbox(v_severity_5748_) as u8);
    v_isSilent_boxed_5756_ = (lean_unbox(v_isSilent_5749_) as u8);
    v_res_5757_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_5746_, v_msgData_5747_, v_severity_boxed_5755_, v_isSilent_boxed_5756_, v___y_5750_, v___y_5751_, v___y_5752_, v___y_5753_);
    lean_dec(v___y_5753_);
    lean_dec_ref(v___y_5752_);
    lean_dec(v___y_5751_);
    lean_dec_ref(v___y_5750_);
    lean_dec(v_ref_5746_);
    return v_res_5757_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(
    mut v_ref_5758_: *mut LeanObject,
    mut v_msgData_5759_: *mut LeanObject,
    mut v___y_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5767_: u8 = 0;
    let mut v___x_5768_: u8 = 0;
    let mut v___x_5769_: *mut LeanObject = core::ptr::null_mut();
    v___x_5767_ = 2;
    v___x_5768_ = 0;
    v___x_5769_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_5758_, v_msgData_5759_, v___x_5767_, v___x_5768_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_);
    return v___x_5769_;
}
pub unsafe fn l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5___boxed(
    mut v_ref_5770_: *mut LeanObject,
    mut v_msgData_5771_: *mut LeanObject,
    mut v___y_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
    mut v___y_5778_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5779_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5777_);
    lean_dec_ref(v___y_5776_);
    lean_dec(v___y_5775_);
    lean_dec_ref(v___y_5774_);
    lean_dec(v___y_5773_);
    lean_dec_ref(v___y_5772_);
    lean_dec(v_ref_5770_);
    return v_res_5779_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(
    mut v_ref_5780_: *mut LeanObject,
    mut v_msgData_5781_: *mut LeanObject,
    mut v___y_5782_: *mut LeanObject,
    mut v___y_5783_: *mut LeanObject,
    mut v___y_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5789_: u8 = 0;
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    v___x_5789_ = 1;
    v___x_5790_ = 0;
    v___x_5791_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_5780_, v_msgData_5781_, v___x_5789_, v___x_5790_, v___y_5784_, v___y_5785_, v___y_5786_, v___y_5787_);
    return v___x_5791_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4___boxed(
    mut v_ref_5792_: *mut LeanObject,
    mut v_msgData_5793_: *mut LeanObject,
    mut v___y_5794_: *mut LeanObject,
    mut v___y_5795_: *mut LeanObject,
    mut v___y_5796_: *mut LeanObject,
    mut v___y_5797_: *mut LeanObject,
    mut v___y_5798_: *mut LeanObject,
    mut v___y_5799_: *mut LeanObject,
    mut v___y_5800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5801_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_5799_);
    lean_dec_ref(v___y_5798_);
    lean_dec(v___y_5797_);
    lean_dec_ref(v___y_5796_);
    lean_dec(v___y_5795_);
    lean_dec_ref(v___y_5794_);
    lean_dec(v_ref_5792_);
    return v_res_5801_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1()
-> *mut LeanObject {
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    v___x_5803_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__0;
    v___x_5804_ = l_Lean_stringToMessageData(v___x_5803_);
    return v___x_5804_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3()
-> *mut LeanObject {
    let mut v___x_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    v___x_5806_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__2;
    v___x_5807_ = l_Lean_stringToMessageData(v___x_5806_);
    return v___x_5807_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5()
-> *mut LeanObject {
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    v___x_5809_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__4;
    v___x_5810_ = l_Lean_stringToMessageData(v___x_5809_);
    return v___x_5810_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7()
-> *mut LeanObject {
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut LeanObject = core::ptr::null_mut();
    v___x_5812_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__6;
    v___x_5813_ = l_Lean_stringToMessageData(v___x_5812_);
    return v___x_5813_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9()
-> *mut LeanObject {
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut LeanObject = core::ptr::null_mut();
    v___x_5815_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__8;
    v___x_5816_ = l_Lean_stringToMessageData(v___x_5815_);
    return v___x_5816_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__11()
-> *mut LeanObject {
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: *mut LeanObject = core::ptr::null_mut();
    v___x_5818_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__10;
    v___x_5819_ = l_Lean_stringToMessageData(v___x_5818_);
    return v___x_5819_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13()
-> *mut LeanObject {
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    v___x_5821_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__12;
    v___x_5822_ = l_Lean_stringToMessageData(v___x_5821_);
    return v___x_5822_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15()
-> *mut LeanObject {
    let mut v___x_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut LeanObject = core::ptr::null_mut();
    v___x_5824_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__14;
    v___x_5825_ = l_Lean_stringToMessageData(v___x_5824_);
    return v___x_5825_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17()
-> *mut LeanObject {
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    v___x_5827_ = l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__16;
    v___x_5828_ = l_Lean_stringToMessageData(v___x_5827_);
    return v___x_5828_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabCheckedNamedError(
    mut v_stx_5829_: *mut LeanObject,
    mut v_expType_x3f_5830_: *mut LeanObject,
    mut v_a_5831_: *mut LeanObject,
    mut v_a_5832_: *mut LeanObject,
    mut v_a_5833_: *mut LeanObject,
    mut v_a_5834_: *mut LeanObject,
    mut v_a_5835_: *mut LeanObject,
    mut v_a_5836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5839_: u8 = 0;
    let mut v___y_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5853_: u8 = 0;
    let mut v___x_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v___y_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5861_: u8 = 0;
    let mut v___y_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_partialId_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5876_: u8 = 0;
    let mut v___x_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_metadata_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_removedVersion_x3f_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5902_: u8 = 0;
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v___x_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v___x_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5920_: u8 = 0;
    let mut v_reuseFailAlloc_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5922_: u8 = 0;
    let mut v_unused_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: u8 = 0;
    let mut v___x_5935_: u8 = 0;
    let mut v___x_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5960_: u8 = 0;
    let mut v___x_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: u8 = 0;
    let mut v___x_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5974_: u8 = 0;
    let mut v___x_5975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: u8 = 0;
    let mut v___x_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5985_: u8 = 0;
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: u8 = 0;
    let mut v___x_5989_: u8 = 0;
    let mut v___x_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6007_: u8 = 0;
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6011_: u8 = 0;
    let mut v_reuseFailAlloc_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6013_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5977_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap;
                lean_inc(v_stx_5829_);
                v___x_5978_ = l_Lean_Syntax_getKind(v_stx_5829_);
                v___x_5979_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_5977_, v___x_5978_);
                lean_dec(v___x_5978_);
                if lean_obj_tag(v___x_5979_) == 1 {
                    v_val_5980_ = lean_ctor_get(v___x_5979_, 0);
                    lean_inc(v_val_5980_);
                    lean_dec_ref_known(v___x_5979_, 1);
                    v_fst_5981_ = lean_ctor_get(v_val_5980_, 0);
                    v_snd_5982_ = lean_ctor_get(v_val_5980_, 1);
                    v_isSharedCheck_6013_ = (!lean_is_exclusive(v_val_5980_)) as u8;
                    if v_isSharedCheck_6013_ == 0 {
                        v___x_5984_ = v_val_5980_;
                        v_isShared_5985_ = v_isSharedCheck_6013_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_snd_5982_);
                        lean_inc(v_fst_5981_);
                        lean_dec(v_val_5980_);
                        v___x_5984_ = lean_box(0);
                        v_isShared_5985_ = v_isSharedCheck_6013_;
                        state = 15;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5979_);
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
                v___x_5846_ = lean_alloc_closure(
                    l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___boxed
                        as *mut core::ffi::c_void,
                    3,
                    1,
                );
                lean_closure_set(v___x_5846_, 0, v_stx_5829_);
                v___x_5847_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v___x_5846_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_);
                if lean_obj_tag(v___x_5847_) == 0 {
                    v_a_5848_ = lean_ctor_get(v___x_5847_, 0);
                    lean_inc(v_a_5848_);
                    lean_dec_ref_known(v___x_5847_, 1);
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
                    lean_dec(v_expType_x3f_5830_);
                    v_a_5850_ = lean_ctor_get(v___x_5847_, 0);
                    v_isSharedCheck_5857_ = (!lean_is_exclusive(v___x_5847_)) as u8;
                    if v_isSharedCheck_5857_ == 0 {
                        v___x_5852_ = v___x_5847_;
                        v_isShared_5853_ = v_isSharedCheck_5857_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5850_);
                        lean_dec(v___x_5847_);
                        v___x_5852_ = lean_box(0);
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
                    v_reuseFailAlloc_5856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5856_, 0, v_a_5850_);
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
                v___x_5869_ = lean_unsigned_to_nat(2);
                v___x_5870_ = lean_nat_sub(v___x_5868_, v___x_5869_);
                lean_dec(v___x_5868_);
                v_partialId_5871_ = l_Lean_Syntax_getArg(v___y_5867_, v___x_5870_);
                lean_dec(v___x_5870_);
                v___x_5872_ = lean_alloc_ctor(6, 2, (0) as u32);
                lean_ctor_set(v___x_5872_, 0, v___y_5867_);
                lean_ctor_set(v___x_5872_, 1, v_partialId_5871_);
                v___x_5873_ = l_Lean_Elab_addCompletionInfo___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__1(v___x_5872_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                v_isSharedCheck_5922_ = (!lean_is_exclusive(v___x_5873_)) as u8;
                if v_isSharedCheck_5922_ == 0 {
                    v_unused_5923_ = lean_ctor_get(v___x_5873_, 0);
                    lean_dec(v_unused_5923_);
                    v___x_5875_ = v___x_5873_;
                    v_isShared_5876_ = v_isSharedCheck_5922_;
                    state = 5;
                    continue;
                } else {
                    lean_dec(v___x_5873_);
                    v___x_5875_ = lean_box(0);
                    v_isShared_5876_ = v_isSharedCheck_5922_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_5877_ = l_Lean_Syntax_getId(v___y_5862_);
                v___x_5878_ = lean_erase_macro_scopes(v___x_5877_);
                lean_inc(v___x_5878_);
                lean_inc(v___y_5862_);
                v___x_5879_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_5879_, 0, v___y_5862_);
                lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                if v_isShared_5876_ == 0 {
                    lean_ctor_set_tag(v___x_5875_, 6);
                    lean_ctor_set(v___x_5875_, 0, v___x_5879_);
                    v___x_5881_ = v___x_5875_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5921_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5921_, 0, v___x_5879_);
                    v___x_5881_ = v_reuseFailAlloc_5921_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_5882_ = l_Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2(v___x_5881_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                lean_dec_ref(v___x_5882_);
                v___x_5883_ = l_Lean_getErrorExplanation_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__3___redArg(v___x_5878_, v___y_5859_);
                v_a_5884_ = lean_ctor_get(v___x_5883_, 0);
                lean_inc(v_a_5884_);
                lean_dec_ref(v___x_5883_);
                if lean_obj_tag(v_a_5884_) == 1 {
                    v_val_5885_ = lean_ctor_get(v_a_5884_, 0);
                    lean_inc(v_val_5885_);
                    lean_dec_ref_known(v_a_5884_, 1);
                    v_metadata_5886_ = lean_ctor_get(v_val_5885_, 1);
                    lean_inc_ref(v_metadata_5886_);
                    lean_dec(v_val_5885_);
                    v_removedVersion_x3f_5887_ = lean_ctor_get(v_metadata_5886_, 2);
                    lean_inc(v_removedVersion_x3f_5887_);
                    lean_dec_ref(v_metadata_5886_);
                    if lean_obj_tag(v_removedVersion_x3f_5887_) == 1 {
                        v_val_5888_ = lean_ctor_get(v_removedVersion_x3f_5887_, 0);
                        lean_inc(v_val_5888_);
                        lean_dec_ref_known(v_removedVersion_x3f_5887_, 1);
                        v___x_5889_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1_once
                            ),
                            _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__1,
                        );
                        v___x_5890_ = l_Lean_MessageData_ofName(v___x_5878_);
                        v___x_5891_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5891_, 0, v___x_5889_);
                        lean_ctor_set(v___x_5891_, 1, v___x_5890_);
                        v___x_5892_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3_once
                            ),
                            _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__3,
                        );
                        v___x_5893_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5893_, 0, v___x_5891_);
                        lean_ctor_set(v___x_5893_, 1, v___x_5892_);
                        v___x_5894_ = l_Lean_stringToMessageData(v_val_5888_);
                        v___x_5895_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5895_, 0, v___x_5893_);
                        lean_ctor_set(v___x_5895_, 1, v___x_5894_);
                        v___x_5896_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5_once
                            ),
                            _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__5,
                        );
                        v___x_5897_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_5897_, 0, v___x_5895_);
                        lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                        v___x_5898_ = l_Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4(v___y_5862_, v___x_5897_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                        lean_dec(v___y_5862_);
                        if lean_obj_tag(v___x_5898_) == 0 {
                            lean_dec_ref_known(v___x_5898_, 1);
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
                            lean_dec(v_expType_x3f_5830_);
                            lean_dec(v_stx_5829_);
                            v_a_5899_ = lean_ctor_get(v___x_5898_, 0);
                            v_isSharedCheck_5906_ = (!lean_is_exclusive(v___x_5898_)) as u8;
                            if v_isSharedCheck_5906_ == 0 {
                                v___x_5901_ = v___x_5898_;
                                v_isShared_5902_ = v_isSharedCheck_5906_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_5899_);
                                lean_dec(v___x_5898_);
                                v___x_5901_ = lean_box(0);
                                v_isShared_5902_ = v_isSharedCheck_5906_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_removedVersion_x3f_5887_);
                        lean_dec(v___x_5878_);
                        lean_dec(v___y_5862_);
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
                    lean_dec(v_a_5884_);
                    v___x_5907_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7_once
                        ),
                        _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__7,
                    );
                    v___x_5908_ = l_Lean_MessageData_ofName(v___x_5878_);
                    v___x_5909_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5909_, 0, v___x_5907_);
                    lean_ctor_set(v___x_5909_, 1, v___x_5908_);
                    v___x_5910_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9_once
                        ),
                        _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__9,
                    );
                    v___x_5911_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_5911_, 0, v___x_5909_);
                    lean_ctor_set(v___x_5911_, 1, v___x_5910_);
                    v___x_5912_ = l_Lean_logErrorAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__5(v___y_5862_, v___x_5911_, v___y_5865_, v___y_5863_, v___y_5860_, v___y_5864_, v___y_5866_, v___y_5859_);
                    lean_dec(v___y_5862_);
                    if lean_obj_tag(v___x_5912_) == 0 {
                        lean_dec_ref_known(v___x_5912_, 1);
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
                        lean_dec(v_expType_x3f_5830_);
                        lean_dec(v_stx_5829_);
                        v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
                        v_isSharedCheck_5920_ = (!lean_is_exclusive(v___x_5912_)) as u8;
                        if v_isSharedCheck_5920_ == 0 {
                            v___x_5915_ = v___x_5912_;
                            v_isShared_5916_ = v_isSharedCheck_5920_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5913_);
                            lean_dec(v___x_5912_);
                            v___x_5915_ = lean_box(0);
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
                    v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
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
                    v_reuseFailAlloc_5919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5919_, 0, v_a_5913_);
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
                    lean_dec(v___x_5933_);
                    lean_inc(v_stx_5829_);
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
                    v___x_5937_ = lean_unsigned_to_nat(1);
                    v___x_5938_ = lean_nat_sub(v___x_5933_, v___x_5937_);
                    lean_dec(v___x_5933_);
                    v___x_5939_ = lean_unsigned_to_nat(0);
                    v___x_5940_ =
                        l_Array_toSubarray___redArg(v___x_5936_, v___x_5939_, v___x_5938_);
                    v___x_5941_ = l_Subarray_copy___redArg(v___x_5940_);
                    lean_inc(v_stx_5829_);
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
                v___x_5950_ = lean_unsigned_to_nat(2);
                v___x_5951_ = l_Lean_Syntax_getArg(v_stx_5829_, v___x_5950_);
                v___x_5952_ = lean_unsigned_to_nat(5);
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
                    lean_inc(v_stx_5829_);
                    v___x_5962_ = l_Lean_Syntax_isOfKind(v_stx_5829_, v___x_5961_);
                    if v___x_5962_ == 0 {
                        v___x_5963_ = lean_unsigned_to_nat(1);
                        v___x_5964_ = l_Lean_Syntax_getArg(v_stx_5829_, v___x_5963_);
                        v___x_5965_ = lean_unsigned_to_nat(4);
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
                lean_inc(v_stx_5829_);
                v___x_5974_ = l_Lean_Syntax_isOfKind(v_stx_5829_, v___x_5973_);
                if v___x_5974_ == 0 {
                    v___x_5975_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
                    lean_inc(v_stx_5829_);
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
                v_env_5987_ = lean_ctor_get(v___x_5986_, 0);
                lean_inc_ref(v_env_5987_);
                lean_dec(v___x_5986_);
                v___x_5988_ = 1;
                lean_inc(v_snd_5982_);
                v___x_5989_ = l_Lean_Environment_contains(v_env_5987_, v_snd_5982_, v___x_5988_);
                if v___x_5989_ == 0 {
                    lean_dec(v_expType_x3f_5830_);
                    lean_dec(v_stx_5829_);
                    v___x_5990_ = lean_obj_once(
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
                        lean_ctor_set_tag(v___x_5984_, 7);
                        lean_ctor_set(v___x_5984_, 1, v___x_5991_);
                        lean_ctor_set(v___x_5984_, 0, v___x_5990_);
                        v___x_5993_ = v___x_5984_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_6012_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6012_, 0, v___x_5990_);
                        lean_ctor_set(v_reuseFailAlloc_6012_, 1, v___x_5991_);
                        v___x_5993_ = v_reuseFailAlloc_6012_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5984_);
                    lean_dec(v_snd_5982_);
                    lean_dec(v_fst_5981_);
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
                v___x_5994_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13_once
                    ),
                    _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__13,
                );
                v___x_5995_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5995_, 0, v___x_5993_);
                lean_ctor_set(v___x_5995_, 1, v___x_5994_);
                v___x_5996_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15_once
                    ),
                    _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__15,
                );
                v___x_5997_ = l_Lean_MessageData_ofName(v_fst_5981_);
                v___x_5998_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_5998_, 0, v___x_5996_);
                lean_ctor_set(v___x_5998_, 1, v___x_5997_);
                v___x_5999_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17_once
                    ),
                    _init_l_Lean_Elab_ErrorExplanation_elabCheckedNamedError___closed__17,
                );
                v___x_6000_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6000_, 0, v___x_5998_);
                lean_ctor_set(v___x_6000_, 1, v___x_5999_);
                v___x_6001_ = l_Lean_MessageData_hint_x27(v___x_6000_);
                v___x_6002_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6002_, 0, v___x_5995_);
                lean_ctor_set(v___x_6002_, 1, v___x_6001_);
                v___x_6003_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v___x_6002_, v_a_5831_, v_a_5832_, v_a_5833_, v_a_5834_, v_a_5835_, v_a_5836_);
                v_a_6004_ = lean_ctor_get(v___x_6003_, 0);
                v_isSharedCheck_6011_ = (!lean_is_exclusive(v___x_6003_)) as u8;
                if v_isSharedCheck_6011_ == 0 {
                    v___x_6006_ = v___x_6003_;
                    v_isShared_6007_ = v_isSharedCheck_6011_;
                    state = 17;
                    continue;
                } else {
                    lean_inc(v_a_6004_);
                    lean_dec(v___x_6003_);
                    v___x_6006_ = lean_box(0);
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
                    v_reuseFailAlloc_6010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6010_, 0, v_a_6004_);
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
    mut v_stx_6014_: *mut LeanObject,
    mut v_expType_x3f_6015_: *mut LeanObject,
    mut v_a_6016_: *mut LeanObject,
    mut v_a_6017_: *mut LeanObject,
    mut v_a_6018_: *mut LeanObject,
    mut v_a_6019_: *mut LeanObject,
    mut v_a_6020_: *mut LeanObject,
    mut v_a_6021_: *mut LeanObject,
    mut v_a_6022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6023_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_6021_);
    lean_dec_ref(v_a_6020_);
    lean_dec(v_a_6019_);
    lean_dec_ref(v_a_6018_);
    lean_dec(v_a_6017_);
    lean_dec_ref(v_a_6016_);
    return v_res_6023_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(
    mut v_00_u03b1_6024_: *mut LeanObject,
    mut v_x_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6028_: *mut LeanObject = core::ptr::null_mut();
    v___x_6028_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___redArg(v_x_6025_, v___y_6027_);
    return v___x_6028_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1___boxed(
    mut v_00_u03b1_6029_: *mut LeanObject,
    mut v_x_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6033_: *mut LeanObject = core::ptr::null_mut();
    v_res_6033_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__1(v_00_u03b1_6029_, v_x_6030_, v___y_6031_, v___y_6032_);
    lean_dec_ref(v___y_6031_);
    lean_dec_ref(v_x_6030_);
    return v_res_6033_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(
    mut v_00_u03b1_6034_: *mut LeanObject,
    mut v_ref_6035_: *mut LeanObject,
    mut v___y_6036_: *mut LeanObject,
    mut v___y_6037_: *mut LeanObject,
    mut v___y_6038_: *mut LeanObject,
    mut v___y_6039_: *mut LeanObject,
    mut v___y_6040_: *mut LeanObject,
    mut v___y_6041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6043_: *mut LeanObject = core::ptr::null_mut();
    v___x_6043_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___redArg(v_ref_6035_);
    return v___x_6043_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6___boxed(
    mut v_00_u03b1_6044_: *mut LeanObject,
    mut v_ref_6045_: *mut LeanObject,
    mut v___y_6046_: *mut LeanObject,
    mut v___y_6047_: *mut LeanObject,
    mut v___y_6048_: *mut LeanObject,
    mut v___y_6049_: *mut LeanObject,
    mut v___y_6050_: *mut LeanObject,
    mut v___y_6051_: *mut LeanObject,
    mut v___y_6052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6053_: *mut LeanObject = core::ptr::null_mut();
    v_res_6053_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__6(v_00_u03b1_6044_, v_ref_6045_, v___y_6046_, v___y_6047_, v___y_6048_, v___y_6049_, v___y_6050_, v___y_6051_);
    lean_dec(v___y_6051_);
    lean_dec_ref(v___y_6050_);
    lean_dec(v___y_6049_);
    lean_dec_ref(v___y_6048_);
    lean_dec(v___y_6047_);
    lean_dec_ref(v___y_6046_);
    return v_res_6053_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(
    mut v_00_u03b1_6054_: *mut LeanObject,
    mut v___y_6055_: *mut LeanObject,
    mut v___y_6056_: *mut LeanObject,
    mut v___y_6057_: *mut LeanObject,
    mut v___y_6058_: *mut LeanObject,
    mut v___y_6059_: *mut LeanObject,
    mut v___y_6060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6062_: *mut LeanObject = core::ptr::null_mut();
    v___x_6062_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg();
    return v___x_6062_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___boxed(
    mut v_00_u03b1_6063_: *mut LeanObject,
    mut v___y_6064_: *mut LeanObject,
    mut v___y_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
    mut v___y_6068_: *mut LeanObject,
    mut v___y_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6071_: *mut LeanObject = core::ptr::null_mut();
    v_res_6071_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7(v_00_u03b1_6063_, v___y_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_);
    lean_dec(v___y_6069_);
    lean_dec_ref(v___y_6068_);
    lean_dec(v___y_6067_);
    lean_dec_ref(v___y_6066_);
    lean_dec(v___y_6065_);
    lean_dec_ref(v___y_6064_);
    return v_res_6071_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0(
    mut v_00_u03b1_6072_: *mut LeanObject,
    mut v_x_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6081_: *mut LeanObject = core::ptr::null_mut();
    v___x_6081_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___redArg(v_x_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_);
    return v___x_6081_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0___boxed(
    mut v_00_u03b1_6082_: *mut LeanObject,
    mut v_x_6083_: *mut LeanObject,
    mut v___y_6084_: *mut LeanObject,
    mut v___y_6085_: *mut LeanObject,
    mut v___y_6086_: *mut LeanObject,
    mut v___y_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
    mut v___y_6089_: *mut LeanObject,
    mut v___y_6090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6091_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6089_);
    lean_dec_ref(v___y_6088_);
    lean_dec(v___y_6087_);
    lean_dec_ref(v___y_6086_);
    lean_dec(v___y_6085_);
    lean_dec_ref(v___y_6084_);
    return v_res_6091_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(
    mut v_t_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
    mut v___y_6095_: *mut LeanObject,
    mut v___y_6096_: *mut LeanObject,
    mut v___y_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6100_: *mut LeanObject = core::ptr::null_mut();
    v___x_6100_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___redArg(v_t_6092_, v___y_6098_);
    return v___x_6100_;
}
pub unsafe fn l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10___boxed(
    mut v_t_6101_: *mut LeanObject,
    mut v___y_6102_: *mut LeanObject,
    mut v___y_6103_: *mut LeanObject,
    mut v___y_6104_: *mut LeanObject,
    mut v___y_6105_: *mut LeanObject,
    mut v___y_6106_: *mut LeanObject,
    mut v___y_6107_: *mut LeanObject,
    mut v___y_6108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6109_: *mut LeanObject = core::ptr::null_mut();
    v_res_6109_ = l_Lean_Elab_pushInfoTree___at___00Lean_Elab_pushInfoLeaf___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__2_spec__10(v_t_6101_, v___y_6102_, v___y_6103_, v___y_6104_, v___y_6105_, v___y_6106_, v___y_6107_);
    lean_dec(v___y_6107_);
    lean_dec_ref(v___y_6106_);
    lean_dec(v___y_6105_);
    lean_dec_ref(v___y_6104_);
    lean_dec(v___y_6103_);
    lean_dec_ref(v___y_6102_);
    return v_res_6109_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(
    mut v_00_u03b2_6110_: *mut LeanObject,
    mut v_m_6111_: *mut LeanObject,
    mut v_a_6112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6113_: *mut LeanObject = core::ptr::null_mut();
    v___x_6113_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v_m_6111_, v_a_6112_);
    return v___x_6113_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___boxed(
    mut v_00_u03b2_6114_: *mut LeanObject,
    mut v_m_6115_: *mut LeanObject,
    mut v_a_6116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6117_: *mut LeanObject = core::ptr::null_mut();
    v_res_6117_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6(v_00_u03b2_6114_, v_m_6115_, v_a_6116_);
    lean_dec(v_a_6116_);
    lean_dec_ref(v_m_6115_);
    return v_res_6117_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7(
    mut v_00_u03b1_6118_: *mut LeanObject,
    mut v_msg_6119_: *mut LeanObject,
    mut v___y_6120_: *mut LeanObject,
    mut v___y_6121_: *mut LeanObject,
    mut v___y_6122_: *mut LeanObject,
    mut v___y_6123_: *mut LeanObject,
    mut v___y_6124_: *mut LeanObject,
    mut v___y_6125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6127_: *mut LeanObject = core::ptr::null_mut();
    v___x_6127_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___redArg(v_msg_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_, v___y_6124_, v___y_6125_);
    return v___x_6127_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7___boxed(
    mut v_00_u03b1_6128_: *mut LeanObject,
    mut v_msg_6129_: *mut LeanObject,
    mut v___y_6130_: *mut LeanObject,
    mut v___y_6131_: *mut LeanObject,
    mut v___y_6132_: *mut LeanObject,
    mut v___y_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
    mut v___y_6135_: *mut LeanObject,
    mut v___y_6136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6137_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6135_);
    lean_dec_ref(v___y_6134_);
    lean_dec(v___y_6133_);
    lean_dec_ref(v___y_6132_);
    lean_dec(v___y_6131_);
    lean_dec_ref(v___y_6130_);
    return v_res_6137_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(
    mut v_cls_6138_: *mut LeanObject,
    mut v_msg_6139_: *mut LeanObject,
    mut v___y_6140_: *mut LeanObject,
    mut v___y_6141_: *mut LeanObject,
    mut v___y_6142_: *mut LeanObject,
    mut v___y_6143_: *mut LeanObject,
    mut v___y_6144_: *mut LeanObject,
    mut v___y_6145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    v___x_6147_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg(v_cls_6138_, v_msg_6139_, v___y_6142_, v___y_6143_, v___y_6144_, v___y_6145_);
    return v___x_6147_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___boxed(
    mut v_cls_6148_: *mut LeanObject,
    mut v_msg_6149_: *mut LeanObject,
    mut v___y_6150_: *mut LeanObject,
    mut v___y_6151_: *mut LeanObject,
    mut v___y_6152_: *mut LeanObject,
    mut v___y_6153_: *mut LeanObject,
    mut v___y_6154_: *mut LeanObject,
    mut v___y_6155_: *mut LeanObject,
    mut v___y_6156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6157_: *mut LeanObject = core::ptr::null_mut();
    v_res_6157_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0(v_cls_6148_, v_msg_6149_, v___y_6150_, v___y_6151_, v___y_6152_, v___y_6153_, v___y_6154_, v___y_6155_);
    lean_dec(v___y_6155_);
    lean_dec_ref(v___y_6154_);
    lean_dec(v___y_6153_);
    lean_dec_ref(v___y_6152_);
    lean_dec(v___y_6151_);
    lean_dec_ref(v___y_6150_);
    return v_res_6157_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(
    mut v_as_6158_: *mut LeanObject,
    mut v_as_x27_6159_: *mut LeanObject,
    mut v_b_6160_: *mut LeanObject,
    mut v_a_6161_: *mut LeanObject,
    mut v___y_6162_: *mut LeanObject,
    mut v___y_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6169_: *mut LeanObject = core::ptr::null_mut();
    v___x_6169_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___redArg(v_as_x27_6159_, v_b_6160_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_);
    return v___x_6169_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3___boxed(
    mut v_as_6170_: *mut LeanObject,
    mut v_as_x27_6171_: *mut LeanObject,
    mut v_b_6172_: *mut LeanObject,
    mut v_a_6173_: *mut LeanObject,
    mut v___y_6174_: *mut LeanObject,
    mut v___y_6175_: *mut LeanObject,
    mut v___y_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6181_: *mut LeanObject = core::ptr::null_mut();
    v_res_6181_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__3(v_as_6170_, v_as_x27_6171_, v_b_6172_, v_a_6173_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
    lean_dec(v___y_6179_);
    lean_dec_ref(v___y_6178_);
    lean_dec(v___y_6177_);
    lean_dec_ref(v___y_6176_);
    lean_dec(v___y_6175_);
    lean_dec_ref(v___y_6174_);
    lean_dec(v_as_x27_6171_);
    lean_dec(v_as_6170_);
    return v_res_6181_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(
    mut v_00_u03b1_6182_: *mut LeanObject,
    mut v_ref_6183_: *mut LeanObject,
    mut v_msg_6184_: *mut LeanObject,
    mut v___y_6185_: *mut LeanObject,
    mut v___y_6186_: *mut LeanObject,
    mut v___y_6187_: *mut LeanObject,
    mut v___y_6188_: *mut LeanObject,
    mut v___y_6189_: *mut LeanObject,
    mut v___y_6190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6192_: *mut LeanObject = core::ptr::null_mut();
    v___x_6192_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___redArg(v_ref_6183_, v_msg_6184_, v___y_6185_, v___y_6186_, v___y_6187_, v___y_6188_, v___y_6189_, v___y_6190_);
    return v___x_6192_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5___boxed(
    mut v_00_u03b1_6193_: *mut LeanObject,
    mut v_ref_6194_: *mut LeanObject,
    mut v_msg_6195_: *mut LeanObject,
    mut v___y_6196_: *mut LeanObject,
    mut v___y_6197_: *mut LeanObject,
    mut v___y_6198_: *mut LeanObject,
    mut v___y_6199_: *mut LeanObject,
    mut v___y_6200_: *mut LeanObject,
    mut v___y_6201_: *mut LeanObject,
    mut v___y_6202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6203_: *mut LeanObject = core::ptr::null_mut();
    v_res_6203_ = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__5(v_00_u03b1_6193_, v_ref_6194_, v_msg_6195_, v___y_6196_, v___y_6197_, v___y_6198_, v___y_6199_, v___y_6200_, v___y_6201_);
    lean_dec(v___y_6201_);
    lean_dec_ref(v___y_6200_);
    lean_dec(v___y_6199_);
    lean_dec_ref(v___y_6198_);
    lean_dec(v___y_6197_);
    lean_dec_ref(v___y_6196_);
    lean_dec(v_ref_6194_);
    return v_res_6203_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(
    mut v_ref_6204_: *mut LeanObject,
    mut v_msgData_6205_: *mut LeanObject,
    mut v_severity_6206_: u8,
    mut v_isSilent_6207_: u8,
    mut v___y_6208_: *mut LeanObject,
    mut v___y_6209_: *mut LeanObject,
    mut v___y_6210_: *mut LeanObject,
    mut v___y_6211_: *mut LeanObject,
    mut v___y_6212_: *mut LeanObject,
    mut v___y_6213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    v___x_6215_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___redArg(v_ref_6204_, v_msgData_6205_, v_severity_6206_, v_isSilent_6207_, v___y_6210_, v___y_6211_, v___y_6212_, v___y_6213_);
    return v___x_6215_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13___boxed(
    mut v_ref_6216_: *mut LeanObject,
    mut v_msgData_6217_: *mut LeanObject,
    mut v_severity_6218_: *mut LeanObject,
    mut v_isSilent_6219_: *mut LeanObject,
    mut v___y_6220_: *mut LeanObject,
    mut v___y_6221_: *mut LeanObject,
    mut v___y_6222_: *mut LeanObject,
    mut v___y_6223_: *mut LeanObject,
    mut v___y_6224_: *mut LeanObject,
    mut v___y_6225_: *mut LeanObject,
    mut v___y_6226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_severity_boxed_6227_: u8 = 0;
    let mut v_isSilent_boxed_6228_: u8 = 0;
    let mut v_res_6229_: *mut LeanObject = core::ptr::null_mut();
    v_severity_boxed_6227_ = (lean_unbox(v_severity_6218_) as u8);
    v_isSilent_boxed_6228_ = (lean_unbox(v_isSilent_6219_) as u8);
    v_res_6229_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13(v_ref_6216_, v_msgData_6217_, v_severity_boxed_6227_, v_isSilent_boxed_6228_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_);
    lean_dec(v___y_6225_);
    lean_dec_ref(v___y_6224_);
    lean_dec(v___y_6223_);
    lean_dec_ref(v___y_6222_);
    lean_dec(v___y_6221_);
    lean_dec_ref(v___y_6220_);
    lean_dec(v_ref_6216_);
    return v_res_6229_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(
    mut v_00_u03b2_6230_: *mut LeanObject,
    mut v_a_6231_: *mut LeanObject,
    mut v_x_6232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6233_: *mut LeanObject = core::ptr::null_mut();
    v___x_6233_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___redArg(v_a_6231_, v_x_6232_);
    return v___x_6233_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16___boxed(
    mut v_00_u03b2_6234_: *mut LeanObject,
    mut v_a_6235_: *mut LeanObject,
    mut v_x_6236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6237_: *mut LeanObject = core::ptr::null_mut();
    v_res_6237_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6_spec__16(v_00_u03b2_6234_, v_a_6235_, v_x_6236_);
    lean_dec(v_x_6236_);
    lean_dec(v_a_6235_);
    return v_res_6237_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(
    mut v_msgData_6238_: *mut LeanObject,
    mut v_macroStack_6239_: *mut LeanObject,
    mut v___y_6240_: *mut LeanObject,
    mut v___y_6241_: *mut LeanObject,
    mut v___y_6242_: *mut LeanObject,
    mut v___y_6243_: *mut LeanObject,
    mut v___y_6244_: *mut LeanObject,
    mut v___y_6245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6247_: *mut LeanObject = core::ptr::null_mut();
    v___x_6247_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg(v_msgData_6238_, v_macroStack_6239_, v___y_6244_);
    return v___x_6247_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___boxed(
    mut v_msgData_6248_: *mut LeanObject,
    mut v_macroStack_6249_: *mut LeanObject,
    mut v___y_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
    mut v___y_6254_: *mut LeanObject,
    mut v___y_6255_: *mut LeanObject,
    mut v___y_6256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6257_: *mut LeanObject = core::ptr::null_mut();
    v_res_6257_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19(v_msgData_6248_, v_macroStack_6249_, v___y_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_);
    lean_dec(v___y_6255_);
    lean_dec_ref(v___y_6254_);
    lean_dec(v___y_6253_);
    lean_dec_ref(v___y_6252_);
    lean_dec(v___y_6251_);
    lean_dec_ref(v___y_6250_);
    return v_res_6257_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(
    mut v_00_u03b2_6258_: *mut LeanObject,
    mut v_x_6259_: *mut LeanObject,
    mut v_x_6260_: *mut LeanObject,
) -> u8 {
    let mut v___x_6261_: u8 = 0;
    v___x_6261_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v_x_6259_, v_x_6260_);
    return v___x_6261_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___boxed(
    mut v_00_u03b2_6262_: *mut LeanObject,
    mut v_x_6263_: *mut LeanObject,
    mut v_x_6264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6265_: u8 = 0;
    let mut v_r_6266_: *mut LeanObject = core::ptr::null_mut();
    v_res_6265_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15(v_00_u03b2_6262_, v_x_6263_, v_x_6264_);
    lean_dec_ref(v_x_6264_);
    lean_dec_ref(v_x_6263_);
    v_r_6266_ = lean_box((v_res_6265_) as usize);
    return v_r_6266_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(
    mut v_00_u03b2_6267_: *mut LeanObject,
    mut v_x_6268_: *mut LeanObject,
    mut v_x_6269_: usize,
    mut v_x_6270_: *mut LeanObject,
) -> u8 {
    let mut v___x_6271_: u8 = 0;
    v___x_6271_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___redArg(v_x_6268_, v_x_6269_, v_x_6270_);
    return v___x_6271_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23___boxed(
    mut v_00_u03b2_6272_: *mut LeanObject,
    mut v_x_6273_: *mut LeanObject,
    mut v_x_6274_: *mut LeanObject,
    mut v_x_6275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_22597__boxed_6276_: usize = 0;
    let mut v_res_6277_: u8 = 0;
    let mut v_r_6278_: *mut LeanObject = core::ptr::null_mut();
    v_x_22597__boxed_6276_ = lean_unbox_usize(v_x_6274_);
    lean_dec(v_x_6274_);
    v_res_6277_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23(v_00_u03b2_6272_, v_x_6273_, v_x_22597__boxed_6276_, v_x_6275_);
    lean_dec_ref(v_x_6275_);
    lean_dec_ref(v_x_6273_);
    v_r_6278_ = lean_box((v_res_6277_) as usize);
    return v_r_6278_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(
    mut v_00_u03b2_6279_: *mut LeanObject,
    mut v_keys_6280_: *mut LeanObject,
    mut v_vals_6281_: *mut LeanObject,
    mut v_heq_6282_: *mut LeanObject,
    mut v_i_6283_: *mut LeanObject,
    mut v_k_6284_: *mut LeanObject,
) -> u8 {
    let mut v___x_6285_: u8 = 0;
    v___x_6285_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___redArg(v_keys_6280_, v_i_6283_, v_k_6284_);
    return v___x_6285_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26___boxed(
    mut v_00_u03b2_6286_: *mut LeanObject,
    mut v_keys_6287_: *mut LeanObject,
    mut v_vals_6288_: *mut LeanObject,
    mut v_heq_6289_: *mut LeanObject,
    mut v_i_6290_: *mut LeanObject,
    mut v_k_6291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6292_: u8 = 0;
    let mut v_r_6293_: *mut LeanObject = core::ptr::null_mut();
    v_res_6292_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15_spec__23_spec__26(v_00_u03b2_6286_, v_keys_6287_, v_vals_6288_, v_heq_6289_, v_i_6290_, v_k_6291_);
    lean_dec_ref(v_k_6291_);
    lean_dec_ref(v_vals_6288_);
    lean_dec_ref(v_keys_6287_);
    v_r_6293_ = lean_box((v_res_6292_) as usize);
    return v_r_6293_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1()
-> *mut LeanObject {
    let mut v___x_6302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    v___x_6302_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6303_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__3;
    v___x_6304_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6305_ = lean_alloc_closure(
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
    mut v_a_6307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6308_: *mut LeanObject = core::ptr::null_mut();
    v_res_6308_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
    return v_res_6308_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3()
-> *mut LeanObject {
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    v___x_6310_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6311_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__5;
    v___x_6312_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6313_ = lean_alloc_closure(
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
    mut v_a_6315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6316_: *mut LeanObject = core::ptr::null_mut();
    v_res_6316_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
    return v_res_6316_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5()
-> *mut LeanObject {
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut LeanObject = core::ptr::null_mut();
    v___x_6318_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6319_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__7;
    v___x_6320_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6321_ = lean_alloc_closure(
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
    mut v_a_6323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6324_: *mut LeanObject = core::ptr::null_mut();
    v_res_6324_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
    return v_res_6324_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7()
-> *mut LeanObject {
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    v___x_6326_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6327_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__9;
    v___x_6328_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6329_ = lean_alloc_closure(
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
    mut v_a_6331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6332_: *mut LeanObject = core::ptr::null_mut();
    v_res_6332_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
    return v_res_6332_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9()
-> *mut LeanObject {
    let mut v___x_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    v___x_6334_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6335_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__11;
    v___x_6336_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6337_ = lean_alloc_closure(
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
    mut v_a_6339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6340_: *mut LeanObject = core::ptr::null_mut();
    v_res_6340_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
    return v_res_6340_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11()
-> *mut LeanObject {
    let mut v___x_6342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    v___x_6342_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_6343_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__13;
    v___x_6344_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1___closed__2;
    v___x_6345_ = lean_alloc_closure(
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
    mut v_a_6347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6348_: *mut LeanObject = core::ptr::null_mut();
    v_res_6348_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
    return v_res_6348_;
}
pub unsafe fn _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut LeanObject = core::ptr::null_mut();
    v___x_6349_ = lean_box(0);
    v___x_6350_ = l_Lean_Elab_abortTermExceptionId;
    v___x_6351_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_6351_, 0, v___x_6350_);
    lean_ctor_set(v___x_6351_, 1, v___x_6349_);
    return v___x_6351_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    v___x_6353_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___closed__0);
    v___x_6354_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6354_, 0, v___x_6353_);
    return v___x_6354_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg___boxed(
    mut v___y_6355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6356_: *mut LeanObject = core::ptr::null_mut();
    v_res_6356_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
    return v_res_6356_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(
    mut v_00_u03b1_6357_: *mut LeanObject,
    mut v___y_6358_: *mut LeanObject,
    mut v___y_6359_: *mut LeanObject,
    mut v___y_6360_: *mut LeanObject,
    mut v___y_6361_: *mut LeanObject,
    mut v___y_6362_: *mut LeanObject,
    mut v___y_6363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6365_: *mut LeanObject = core::ptr::null_mut();
    v___x_6365_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___redArg();
    return v___x_6365_;
}
pub unsafe fn l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0___boxed(
    mut v_00_u03b1_6366_: *mut LeanObject,
    mut v___y_6367_: *mut LeanObject,
    mut v___y_6368_: *mut LeanObject,
    mut v___y_6369_: *mut LeanObject,
    mut v___y_6370_: *mut LeanObject,
    mut v___y_6371_: *mut LeanObject,
    mut v___y_6372_: *mut LeanObject,
    mut v___y_6373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6374_: *mut LeanObject = core::ptr::null_mut();
    v_res_6374_ = l_Lean_Elab_throwAbortTerm___at___00__private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1_spec__0(v_00_u03b1_6366_, v___y_6367_, v___y_6368_, v___y_6369_, v___y_6370_, v___y_6371_, v___y_6372_);
    lean_dec(v___y_6372_);
    lean_dec_ref(v___y_6371_);
    lean_dec(v___y_6370_);
    lean_dec_ref(v___y_6369_);
    lean_dec(v___y_6368_);
    lean_dec_ref(v___y_6367_);
    return v_res_6374_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(
    mut v_t_6375_: *mut LeanObject,
    mut v_tp_6376_: *mut LeanObject,
    mut v_a_6377_: *mut LeanObject,
    mut v_a_6378_: *mut LeanObject,
    mut v_a_6379_: *mut LeanObject,
    mut v_a_6380_: *mut LeanObject,
    mut v_a_6381_: *mut LeanObject,
    mut v_a_6382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: u8 = 0;
    let mut v___x_6386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: u8 = 0;
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: u8 = 0;
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6401_: u8 = 0;
    let mut v___x_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut v_a_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v___x_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_tp_6376_);
                v___x_6384_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6384_, 0, v_tp_6376_);
                v___x_6385_ = 1;
                v___x_6386_ = lean_box(0);
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
                if lean_obj_tag(v___x_6387_) == 0 {
                    v_a_6388_ = lean_ctor_get(v___x_6387_, 0);
                    lean_inc(v_a_6388_);
                    lean_dec_ref_known(v___x_6387_, 1);
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
                        if lean_obj_tag(v___x_6397_) == 0 {
                            lean_dec_ref_known(v___x_6397_, 1);
                            v___y_6390_ = v_a_6379_;
                            v___y_6391_ = v_a_6380_;
                            v___y_6392_ = v_a_6381_;
                            v___y_6393_ = v_a_6382_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_a_6388_);
                            lean_dec_ref(v_tp_6376_);
                            v_a_6398_ = lean_ctor_get(v___x_6397_, 0);
                            v_isSharedCheck_6405_ = (!lean_is_exclusive(v___x_6397_)) as u8;
                            if v_isSharedCheck_6405_ == 0 {
                                v___x_6400_ = v___x_6397_;
                                v_isShared_6401_ = v_isSharedCheck_6405_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_6398_);
                                lean_dec(v___x_6397_);
                                v___x_6400_ = lean_box(0);
                                v_isShared_6401_ = v_isSharedCheck_6405_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_tp_6376_);
                    v_a_6406_ = lean_ctor_get(v___x_6387_, 0);
                    v_isSharedCheck_6413_ = (!lean_is_exclusive(v___x_6387_)) as u8;
                    if v_isSharedCheck_6413_ == 0 {
                        v___x_6408_ = v___x_6387_;
                        v_isShared_6409_ = v_isSharedCheck_6413_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6406_);
                        lean_dec(v___x_6387_);
                        v___x_6408_ = lean_box(0);
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
                    v_reuseFailAlloc_6404_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_a_6398_);
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
                    v_reuseFailAlloc_6412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6412_, 0, v_a_6406_);
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
    mut v_t_6414_: *mut LeanObject,
    mut v_tp_6415_: *mut LeanObject,
    mut v_a_6416_: *mut LeanObject,
    mut v_a_6417_: *mut LeanObject,
    mut v_a_6418_: *mut LeanObject,
    mut v_a_6419_: *mut LeanObject,
    mut v_a_6420_: *mut LeanObject,
    mut v_a_6421_: *mut LeanObject,
    mut v_a_6422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6423_: *mut LeanObject = core::ptr::null_mut();
    v_res_6423_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_6414_, v_tp_6415_, v_a_6416_, v_a_6417_, v_a_6418_, v_a_6419_, v_a_6420_, v_a_6421_);
    lean_dec(v_a_6421_);
    lean_dec_ref(v_a_6420_);
    lean_dec(v_a_6419_);
    lean_dec_ref(v_a_6418_);
    lean_dec(v_a_6417_);
    lean_dec_ref(v_a_6416_);
    return v_res_6423_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut LeanObject = core::ptr::null_mut();
    v___x_6425_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__7___redArg___closed__0);
    v___x_6426_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6426_, 0, v___x_6425_);
    return v___x_6426_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg___boxed(
    mut v___y_6427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6428_: *mut LeanObject = core::ptr::null_mut();
    v_res_6428_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
    return v_res_6428_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(
    mut v_00_u03b1_6429_: *mut LeanObject,
    mut v___y_6430_: *mut LeanObject,
    mut v___y_6431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    v___x_6433_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
    return v___x_6433_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___boxed(
    mut v_00_u03b1_6434_: *mut LeanObject,
    mut v___y_6435_: *mut LeanObject,
    mut v___y_6436_: *mut LeanObject,
    mut v___y_6437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6438_: *mut LeanObject = core::ptr::null_mut();
    v_res_6438_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0(v_00_u03b1_6434_, v___y_6435_, v___y_6436_);
    lean_dec(v___y_6436_);
    lean_dec_ref(v___y_6435_);
    return v_res_6438_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(
    mut v___y_6439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mainModule_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    v___x_6441_ = lean_st_ref_get(v___y_6439_);
    v_env_6442_ = lean_ctor_get(v___x_6441_, 0);
    lean_inc_ref(v_env_6442_);
    lean_dec(v___x_6441_);
    v___x_6443_ = l_Lean_Environment_header(v_env_6442_);
    lean_dec_ref(v_env_6442_);
    v_mainModule_6444_ = lean_ctor_get(v___x_6443_, 0);
    lean_inc(v_mainModule_6444_);
    lean_dec_ref(v___x_6443_);
    v___x_6445_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6445_, 0, v_mainModule_6444_);
    return v___x_6445_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg___boxed(
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6448_: *mut LeanObject = core::ptr::null_mut();
    v_res_6448_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_6446_);
    lean_dec(v___y_6446_);
    return v_res_6448_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(
    mut v___y_6449_: *mut LeanObject,
    mut v___y_6450_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    v___x_6452_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_6450_);
    return v___x_6452_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___boxed(
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
    mut v___y_6455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6456_: *mut LeanObject = core::ptr::null_mut();
    v_res_6456_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2(v___y_6453_, v___y_6454_);
    lean_dec(v___y_6454_);
    lean_dec_ref(v___y_6453_);
    return v_res_6456_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0(
    mut v_t_6457_: *mut LeanObject,
    mut v___x_6458_: *mut LeanObject,
    mut v_x_6459_: *mut LeanObject,
    mut v___y_6460_: *mut LeanObject,
    mut v___y_6461_: *mut LeanObject,
    mut v___y_6462_: *mut LeanObject,
    mut v___y_6463_: *mut LeanObject,
    mut v___y_6464_: *mut LeanObject,
    mut v___y_6465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6467_: *mut LeanObject = core::ptr::null_mut();
    v___x_6467_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_unsafe__1(v_t_6457_, v___x_6458_, v___y_6460_, v___y_6461_, v___y_6462_, v___y_6463_, v___y_6464_, v___y_6465_);
    return v___x_6467_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed(
    mut v_t_6468_: *mut LeanObject,
    mut v___x_6469_: *mut LeanObject,
    mut v_x_6470_: *mut LeanObject,
    mut v___y_6471_: *mut LeanObject,
    mut v___y_6472_: *mut LeanObject,
    mut v___y_6473_: *mut LeanObject,
    mut v___y_6474_: *mut LeanObject,
    mut v___y_6475_: *mut LeanObject,
    mut v___y_6476_: *mut LeanObject,
    mut v___y_6477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6478_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_6476_);
    lean_dec_ref(v___y_6475_);
    lean_dec(v___y_6474_);
    lean_dec_ref(v___y_6473_);
    lean_dec(v___y_6472_);
    lean_dec_ref(v___y_6471_);
    lean_dec_ref(v_x_6470_);
    return v_res_6478_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(
    mut v_msgData_6479_: *mut LeanObject,
    mut v_macroStack_6480_: *mut LeanObject,
    mut v___y_6481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: u8 = 0;
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_after_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6496_: u8 = 0;
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msgData_6504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6508_: u8 = 0;
    let mut v_unused_6509_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6483_ = lean_st_ref_get(v___y_6481_);
                v_scopes_6484_ = lean_ctor_get(v___x_6483_, 2);
                lean_inc(v_scopes_6484_);
                lean_dec(v___x_6483_);
                v___x_6485_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_6486_ = l_List_head_x21___redArg(v___x_6485_, v_scopes_6484_);
                lean_dec(v_scopes_6484_);
                v_opts_6487_ = lean_ctor_get(v___x_6486_, 1);
                lean_inc_ref(v_opts_6487_);
                lean_dec(v___x_6486_);
                v___x_6488_ = l_Lean_Elab_pp_macroStack;
                v___x_6489_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__4_spec__13_spec__16(v_opts_6487_, v___x_6488_);
                lean_dec_ref(v_opts_6487_);
                if v___x_6489_ == 0 {
                    lean_dec(v_macroStack_6480_);
                    v___x_6490_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6490_, 0, v_msgData_6479_);
                    return v___x_6490_;
                } else {
                    if lean_obj_tag(v_macroStack_6480_) == 0 {
                        v___x_6491_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6491_, 0, v_msgData_6479_);
                        return v___x_6491_;
                    } else {
                        v_head_6492_ = lean_ctor_get(v_macroStack_6480_, 0);
                        lean_inc(v_head_6492_);
                        v_after_6493_ = lean_ctor_get(v_head_6492_, 1);
                        v_isSharedCheck_6508_ = (!lean_is_exclusive(v_head_6492_)) as u8;
                        if v_isSharedCheck_6508_ == 0 {
                            v_unused_6509_ = lean_ctor_get(v_head_6492_, 0);
                            lean_dec(v_unused_6509_);
                            v___x_6495_ = v_head_6492_;
                            v_isShared_6496_ = v_isSharedCheck_6508_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_after_6493_);
                            lean_dec(v_head_6492_);
                            v___x_6495_ = lean_box(0);
                            v_isShared_6496_ = v_isSharedCheck_6508_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_6497_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23___closed__0);
                if v_isShared_6496_ == 0 {
                    lean_ctor_set_tag(v___x_6495_, 7);
                    lean_ctor_set(v___x_6495_, 1, v___x_6497_);
                    lean_ctor_set(v___x_6495_, 0, v_msgData_6479_);
                    v___x_6499_ = v___x_6495_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6507_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_msgData_6479_);
                    lean_ctor_set(v_reuseFailAlloc_6507_, 1, v___x_6497_);
                    v___x_6499_ = v_reuseFailAlloc_6507_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6500_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19___redArg___closed__2);
                v___x_6501_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6501_, 0, v___x_6499_);
                lean_ctor_set(v___x_6501_, 1, v___x_6500_);
                v___x_6502_ = l_Lean_MessageData_ofSyntax(v_after_6493_);
                v___x_6503_ = l_Lean_indentD(v___x_6502_);
                v_msgData_6504_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v_msgData_6504_, 0, v___x_6501_);
                lean_ctor_set(v_msgData_6504_, 1, v___x_6503_);
                v___x_6505_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__7_spec__19_spec__23(v_msgData_6504_, v_macroStack_6480_);
                v___x_6506_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6506_, 0, v___x_6505_);
                return v___x_6506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg___boxed(
    mut v_msgData_6510_: *mut LeanObject,
    mut v_macroStack_6511_: *mut LeanObject,
    mut v___y_6512_: *mut LeanObject,
    mut v___y_6513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6514_: *mut LeanObject = core::ptr::null_mut();
    v_res_6514_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_6510_, v_macroStack_6511_, v___y_6512_);
    lean_dec(v___y_6512_);
    return v_res_6514_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    v___x_6515_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_6515_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: *mut LeanObject = core::ptr::null_mut();
    v___x_6516_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__0);
    v___x_6517_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6517_, 0, v___x_6516_);
    return v___x_6517_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    v___x_6518_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
    v___x_6519_ = lean_unsigned_to_nat(0);
    v___x_6520_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_6520_, 0, v___x_6519_);
    lean_ctor_set(v___x_6520_, 1, v___x_6519_);
    lean_ctor_set(v___x_6520_, 2, v___x_6519_);
    lean_ctor_set(v___x_6520_, 3, v___x_6519_);
    lean_ctor_set(v___x_6520_, 4, v___x_6518_);
    lean_ctor_set(v___x_6520_, 5, v___x_6518_);
    lean_ctor_set(v___x_6520_, 6, v___x_6518_);
    lean_ctor_set(v___x_6520_, 7, v___x_6518_);
    lean_ctor_set(v___x_6520_, 8, v___x_6518_);
    lean_ctor_set(v___x_6520_, 9, v___x_6518_);
    return v___x_6520_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    v___x_6521_ = lean_unsigned_to_nat(32);
    v___x_6522_ = lean_mk_empty_array_with_capacity(v___x_6521_);
    v___x_6523_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6523_, 0, v___x_6522_);
    return v___x_6523_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6524_: usize = 0;
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    v___x_6524_ = 5usize;
    v___x_6525_ = lean_unsigned_to_nat(0);
    v___x_6526_ = lean_unsigned_to_nat(32);
    v___x_6527_ = lean_mk_empty_array_with_capacity(v___x_6526_);
    v___x_6528_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__3);
    v___x_6529_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_6529_, 0, v___x_6528_);
    lean_ctor_set(v___x_6529_, 1, v___x_6527_);
    lean_ctor_set(v___x_6529_, 2, v___x_6525_);
    lean_ctor_set(v___x_6529_, 3, v___x_6525_);
    lean_ctor_set_usize(v___x_6529_, 4, v___x_6524_);
    return v___x_6529_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut LeanObject = core::ptr::null_mut();
    v___x_6530_ = lean_box(1);
    v___x_6531_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__4);
    v___x_6532_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__1);
    v___x_6533_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_6533_, 0, v___x_6532_);
    lean_ctor_set(v___x_6533_, 1, v___x_6531_);
    lean_ctor_set(v___x_6533_, 2, v___x_6530_);
    return v___x_6533_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(
    mut v_msgData_6534_: *mut LeanObject,
    mut v___y_6535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut LeanObject = core::ptr::null_mut();
    v___x_6537_ = lean_st_ref_get(v___y_6535_);
    v_env_6538_ = lean_ctor_get(v___x_6537_, 0);
    lean_inc_ref(v_env_6538_);
    lean_dec(v___x_6537_);
    v___x_6539_ = lean_st_ref_get(v___y_6535_);
    v_scopes_6540_ = lean_ctor_get(v___x_6539_, 2);
    lean_inc(v_scopes_6540_);
    lean_dec(v___x_6539_);
    v___x_6541_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_6542_ = l_List_head_x21___redArg(v___x_6541_, v_scopes_6540_);
    lean_dec(v_scopes_6540_);
    v_opts_6543_ = lean_ctor_get(v___x_6542_, 1);
    lean_inc_ref(v_opts_6543_);
    lean_dec(v___x_6542_);
    v___x_6544_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__2);
    v___x_6545_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___closed__5);
    v___x_6546_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_6546_, 0, v_env_6538_);
    lean_ctor_set(v___x_6546_, 1, v___x_6544_);
    lean_ctor_set(v___x_6546_, 2, v___x_6545_);
    lean_ctor_set(v___x_6546_, 3, v_opts_6543_);
    v___x_6547_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_6547_, 0, v___x_6546_);
    lean_ctor_set(v___x_6547_, 1, v_msgData_6534_);
    v___x_6548_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_6548_, 0, v___x_6547_);
    return v___x_6548_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg___boxed(
    mut v_msgData_6549_: *mut LeanObject,
    mut v___y_6550_: *mut LeanObject,
    mut v___y_6551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6552_: *mut LeanObject = core::ptr::null_mut();
    v_res_6552_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_6549_, v___y_6550_);
    lean_dec(v___y_6550_);
    return v_res_6552_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(
    mut v_msg_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6567_: u8 = 0;
    let mut v___x_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6572_: u8 = 0;
    let mut v_a_6573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6576_: u8 = 0;
    let mut v___x_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6580_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6557_ = l_Lean_Elab_Command_getRef___redArg(v___y_6554_);
                if lean_obj_tag(v___x_6557_) == 0 {
                    v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
                    lean_inc(v_a_6558_);
                    lean_dec_ref_known(v___x_6557_, 1);
                    v_macroStack_6559_ = lean_ctor_get(v___y_6554_, 4);
                    v___x_6560_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_6553_, v___y_6555_);
                    v_a_6561_ = lean_ctor_get(v___x_6560_, 0);
                    lean_inc(v_a_6561_);
                    lean_dec_ref(v___x_6560_);
                    v___x_6562_ = l_Lean_Elab_getBetterRef(v_a_6558_, v_macroStack_6559_);
                    lean_dec(v_a_6558_);
                    lean_inc(v_macroStack_6559_);
                    v___x_6563_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_a_6561_, v_macroStack_6559_, v___y_6555_);
                    v_a_6564_ = lean_ctor_get(v___x_6563_, 0);
                    v_isSharedCheck_6572_ = (!lean_is_exclusive(v___x_6563_)) as u8;
                    if v_isSharedCheck_6572_ == 0 {
                        v___x_6566_ = v___x_6563_;
                        v_isShared_6567_ = v_isSharedCheck_6572_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6564_);
                        lean_dec(v___x_6563_);
                        v___x_6566_ = lean_box(0);
                        v_isShared_6567_ = v_isSharedCheck_6572_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_6553_);
                    v_a_6573_ = lean_ctor_get(v___x_6557_, 0);
                    v_isSharedCheck_6580_ = (!lean_is_exclusive(v___x_6557_)) as u8;
                    if v_isSharedCheck_6580_ == 0 {
                        v___x_6575_ = v___x_6557_;
                        v_isShared_6576_ = v_isSharedCheck_6580_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6573_);
                        lean_dec(v___x_6557_);
                        v___x_6575_ = lean_box(0);
                        v_isShared_6576_ = v_isSharedCheck_6580_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6568_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6568_, 0, v___x_6562_);
                lean_ctor_set(v___x_6568_, 1, v_a_6564_);
                if v_isShared_6567_ == 0 {
                    lean_ctor_set_tag(v___x_6566_, 1);
                    lean_ctor_set(v___x_6566_, 0, v___x_6568_);
                    v___x_6570_ = v___x_6566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6571_, 0, v___x_6568_);
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
                    v_reuseFailAlloc_6579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6579_, 0, v_a_6573_);
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
    mut v_msg_6581_: *mut LeanObject,
    mut v___y_6582_: *mut LeanObject,
    mut v___y_6583_: *mut LeanObject,
    mut v___y_6584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6585_: *mut LeanObject = core::ptr::null_mut();
    v_res_6585_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_6581_, v___y_6582_, v___y_6583_);
    lean_dec(v___y_6583_);
    lean_dec_ref(v___y_6582_);
    return v_res_6585_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(
    mut v_ref_6586_: *mut LeanObject,
    mut v_msg_6587_: *mut LeanObject,
    mut v___y_6588_: *mut LeanObject,
    mut v___y_6589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_6596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6602_: u8 = 0;
    let mut v_ref_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6609_: u8 = 0;
    let mut v___x_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6613_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6591_ = l_Lean_Elab_Command_getRef___redArg(v___y_6588_);
                if lean_obj_tag(v___x_6591_) == 0 {
                    v_a_6592_ = lean_ctor_get(v___x_6591_, 0);
                    lean_inc(v_a_6592_);
                    lean_dec_ref_known(v___x_6591_, 1);
                    v_fileName_6593_ = lean_ctor_get(v___y_6588_, 0);
                    v_fileMap_6594_ = lean_ctor_get(v___y_6588_, 1);
                    v_currRecDepth_6595_ = lean_ctor_get(v___y_6588_, 2);
                    v_cmdPos_6596_ = lean_ctor_get(v___y_6588_, 3);
                    v_macroStack_6597_ = lean_ctor_get(v___y_6588_, 4);
                    v_quotContext_x3f_6598_ = lean_ctor_get(v___y_6588_, 5);
                    v_currMacroScope_6599_ = lean_ctor_get(v___y_6588_, 6);
                    v_snap_x3f_6600_ = lean_ctor_get(v___y_6588_, 8);
                    v_cancelTk_x3f_6601_ = lean_ctor_get(v___y_6588_, 9);
                    v_suppressElabErrors_6602_ = lean_ctor_get_uint8(
                        v___y_6588_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                    );
                    v_ref_6603_ = l_Lean_replaceRef(v_ref_6586_, v_a_6592_);
                    lean_dec(v_a_6592_);
                    lean_inc(v_cancelTk_x3f_6601_);
                    lean_inc(v_snap_x3f_6600_);
                    lean_inc(v_currMacroScope_6599_);
                    lean_inc(v_quotContext_x3f_6598_);
                    lean_inc(v_macroStack_6597_);
                    lean_inc(v_cmdPos_6596_);
                    lean_inc(v_currRecDepth_6595_);
                    lean_inc_ref(v_fileMap_6594_);
                    lean_inc_ref(v_fileName_6593_);
                    v___x_6604_ = lean_alloc_ctor(0, 10, (1) as u32);
                    lean_ctor_set(v___x_6604_, 0, v_fileName_6593_);
                    lean_ctor_set(v___x_6604_, 1, v_fileMap_6594_);
                    lean_ctor_set(v___x_6604_, 2, v_currRecDepth_6595_);
                    lean_ctor_set(v___x_6604_, 3, v_cmdPos_6596_);
                    lean_ctor_set(v___x_6604_, 4, v_macroStack_6597_);
                    lean_ctor_set(v___x_6604_, 5, v_quotContext_x3f_6598_);
                    lean_ctor_set(v___x_6604_, 6, v_currMacroScope_6599_);
                    lean_ctor_set(v___x_6604_, 7, v_ref_6603_);
                    lean_ctor_set(v___x_6604_, 8, v_snap_x3f_6600_);
                    lean_ctor_set(v___x_6604_, 9, v_cancelTk_x3f_6601_);
                    lean_ctor_set_uint8(
                        v___x_6604_,
                        (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                        v_suppressElabErrors_6602_,
                    );
                    v___x_6605_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_6587_, v___x_6604_, v___y_6589_);
                    lean_dec_ref_known(v___x_6604_, 10);
                    return v___x_6605_;
                } else {
                    lean_dec_ref(v_msg_6587_);
                    v_a_6606_ = lean_ctor_get(v___x_6591_, 0);
                    v_isSharedCheck_6613_ = (!lean_is_exclusive(v___x_6591_)) as u8;
                    if v_isSharedCheck_6613_ == 0 {
                        v___x_6608_ = v___x_6591_;
                        v_isShared_6609_ = v_isSharedCheck_6613_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6606_);
                        lean_dec(v___x_6591_);
                        v___x_6608_ = lean_box(0);
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
                    v_reuseFailAlloc_6612_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_a_6606_);
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
    mut v_ref_6614_: *mut LeanObject,
    mut v_msg_6615_: *mut LeanObject,
    mut v___y_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6619_: *mut LeanObject = core::ptr::null_mut();
    v_res_6619_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_6614_, v_msg_6615_, v___y_6616_, v___y_6617_);
    lean_dec(v___y_6617_);
    lean_dec_ref(v___y_6616_);
    lean_dec(v_ref_6614_);
    return v_res_6619_;
}
pub unsafe fn l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(
    mut v_cls_6620_: *mut LeanObject,
    mut v_msg_6621_: *mut LeanObject,
    mut v___y_6622_: *mut LeanObject,
    mut v___y_6623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6646_: u8 = 0;
    let mut v_tid_6647_: u64 = 0;
    let mut v_traces_6648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: f64 = 0.0;
    let mut v___x_6654_: u8 = 0;
    let mut v___x_6655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6672_: u8 = 0;
    let mut v_isSharedCheck_6673_: u8 = 0;
    let mut v_isSharedCheck_6674_: u8 = 0;
    let mut v_a_6675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6678_: u8 = 0;
    let mut v___x_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6682_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6625_ = l_Lean_Elab_Command_getRef___redArg(v___y_6622_);
                if lean_obj_tag(v___x_6625_) == 0 {
                    v_a_6626_ = lean_ctor_get(v___x_6625_, 0);
                    lean_inc(v_a_6626_);
                    lean_dec_ref_known(v___x_6625_, 1);
                    v___x_6627_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msg_6621_, v___y_6623_);
                    v_a_6628_ = lean_ctor_get(v___x_6627_, 0);
                    v_isSharedCheck_6674_ = (!lean_is_exclusive(v___x_6627_)) as u8;
                    if v_isSharedCheck_6674_ == 0 {
                        v___x_6630_ = v___x_6627_;
                        v_isShared_6631_ = v_isSharedCheck_6674_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6628_);
                        lean_dec(v___x_6627_);
                        v___x_6630_ = lean_box(0);
                        v_isShared_6631_ = v_isSharedCheck_6674_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_msg_6621_);
                    lean_dec(v_cls_6620_);
                    v_a_6675_ = lean_ctor_get(v___x_6625_, 0);
                    v_isSharedCheck_6682_ = (!lean_is_exclusive(v___x_6625_)) as u8;
                    if v_isSharedCheck_6682_ == 0 {
                        v___x_6677_ = v___x_6625_;
                        v_isShared_6678_ = v_isSharedCheck_6682_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_6675_);
                        lean_dec(v___x_6625_);
                        v___x_6677_ = lean_box(0);
                        v_isShared_6678_ = v_isSharedCheck_6682_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6632_ = lean_st_ref_take(v___y_6623_);
                v_traceState_6633_ = lean_ctor_get(v___x_6632_, 9);
                v_env_6634_ = lean_ctor_get(v___x_6632_, 0);
                v_messages_6635_ = lean_ctor_get(v___x_6632_, 1);
                v_scopes_6636_ = lean_ctor_get(v___x_6632_, 2);
                v_usedQuotCtxts_6637_ = lean_ctor_get(v___x_6632_, 3);
                v_nextMacroScope_6638_ = lean_ctor_get(v___x_6632_, 4);
                v_maxRecDepth_6639_ = lean_ctor_get(v___x_6632_, 5);
                v_ngen_6640_ = lean_ctor_get(v___x_6632_, 6);
                v_auxDeclNGen_6641_ = lean_ctor_get(v___x_6632_, 7);
                v_infoState_6642_ = lean_ctor_get(v___x_6632_, 8);
                v_snapshotTasks_6643_ = lean_ctor_get(v___x_6632_, 10);
                v_isSharedCheck_6673_ = (!lean_is_exclusive(v___x_6632_)) as u8;
                if v_isSharedCheck_6673_ == 0 {
                    v___x_6645_ = v___x_6632_;
                    v_isShared_6646_ = v_isSharedCheck_6673_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6643_);
                    lean_inc(v_traceState_6633_);
                    lean_inc(v_infoState_6642_);
                    lean_inc(v_auxDeclNGen_6641_);
                    lean_inc(v_ngen_6640_);
                    lean_inc(v_maxRecDepth_6639_);
                    lean_inc(v_nextMacroScope_6638_);
                    lean_inc(v_usedQuotCtxts_6637_);
                    lean_inc(v_scopes_6636_);
                    lean_inc(v_messages_6635_);
                    lean_inc(v_env_6634_);
                    lean_dec(v___x_6632_);
                    v___x_6645_ = lean_box(0);
                    v_isShared_6646_ = v_isSharedCheck_6673_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6647_ = lean_ctor_get_uint64(
                    v_traceState_6633_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_6648_ = lean_ctor_get(v_traceState_6633_, 0);
                v_isSharedCheck_6672_ = (!lean_is_exclusive(v_traceState_6633_)) as u8;
                if v_isSharedCheck_6672_ == 0 {
                    v___x_6650_ = v_traceState_6633_;
                    v_isShared_6651_ = v_isSharedCheck_6672_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_traces_6648_);
                    lean_dec(v_traceState_6633_);
                    v___x_6650_ = lean_box(0);
                    v_isShared_6651_ = v_isSharedCheck_6672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6652_ = lean_box(0);
                v___x_6653_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__0);
                v___x_6654_ = 0;
                v___x_6655_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                v___x_6656_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_6656_, 0, v_cls_6620_);
                lean_ctor_set(v___x_6656_, 1, v___x_6652_);
                lean_ctor_set(v___x_6656_, 2, v___x_6655_);
                lean_ctor_set_float(
                    v___x_6656_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_6653_,
                );
                lean_ctor_set_float(
                    v___x_6656_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_6653_,
                );
                lean_ctor_set_uint8(
                    v___x_6656_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_6654_,
                );
                v___x_6657_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__2;
                v___x_6658_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_6658_, 0, v___x_6656_);
                lean_ctor_set(v___x_6658_, 1, v_a_6628_);
                lean_ctor_set(v___x_6658_, 2, v___x_6657_);
                v___x_6659_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6659_, 0, v_a_6626_);
                lean_ctor_set(v___x_6659_, 1, v___x_6658_);
                v___x_6660_ = l_Lean_PersistentArray_push___redArg(v_traces_6648_, v___x_6659_);
                if v_isShared_6651_ == 0 {
                    lean_ctor_set(v___x_6650_, 0, v___x_6660_);
                    v___x_6662_ = v___x_6650_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6671_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6671_, 0, v___x_6660_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_6671_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_6647_,
                    );
                    v___x_6662_ = v_reuseFailAlloc_6671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6646_ == 0 {
                    lean_ctor_set(v___x_6645_, 9, v___x_6662_);
                    v___x_6664_ = v___x_6645_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6670_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 0, v_env_6634_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 1, v_messages_6635_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 2, v_scopes_6636_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 3, v_usedQuotCtxts_6637_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 4, v_nextMacroScope_6638_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 5, v_maxRecDepth_6639_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 6, v_ngen_6640_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 7, v_auxDeclNGen_6641_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 8, v_infoState_6642_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 9, v___x_6662_);
                    lean_ctor_set(v_reuseFailAlloc_6670_, 10, v_snapshotTasks_6643_);
                    v___x_6664_ = v_reuseFailAlloc_6670_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6665_ = lean_st_ref_set(v___y_6623_, v___x_6664_);
                v___x_6666_ = lean_box(0);
                if v_isShared_6631_ == 0 {
                    lean_ctor_set(v___x_6630_, 0, v___x_6666_);
                    v___x_6668_ = v___x_6630_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6669_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6669_, 0, v___x_6666_);
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
                    v_reuseFailAlloc_6681_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6681_, 0, v_a_6675_);
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
    mut v_cls_6683_: *mut LeanObject,
    mut v_msg_6684_: *mut LeanObject,
    mut v___y_6685_: *mut LeanObject,
    mut v___y_6686_: *mut LeanObject,
    mut v___y_6687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6688_: *mut LeanObject = core::ptr::null_mut();
    v_res_6688_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_6683_, v_msg_6684_, v___y_6685_, v___y_6686_);
    lean_dec(v___y_6686_);
    lean_dec_ref(v___y_6685_);
    return v_res_6688_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(
    mut v_mod_6689_: *mut LeanObject,
    mut v_isMeta_6690_: u8,
    mut v_hint_6691_: *mut LeanObject,
    mut v___y_6692_: *mut LeanObject,
    mut v___y_6693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6697_: u8 = 0;
    let mut v___x_6698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_entry_6701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6722_: u8 = 0;
    let mut v_asyncMode_6723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6731_: u8 = 0;
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: u8 = 0;
    let mut v___x_6734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_opts_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6741_: u8 = 0;
    let mut v_cls_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: u8 = 0;
    let mut v___x_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6763_: u8 = 0;
    let mut v___x_6764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6695_ = lean_st_ref_get(v___y_6693_);
                v_env_6696_ = lean_ctor_get(v___x_6695_, 0);
                lean_inc_ref(v_env_6696_);
                lean_dec(v___x_6695_);
                v_isExporting_6697_ = lean_ctor_get_uint8(
                    v_env_6696_,
                    (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                );
                lean_dec_ref(v_env_6696_);
                v___x_6698_ = lean_st_ref_get(v___y_6693_);
                v_env_6699_ = lean_ctor_get(v___x_6698_, 0);
                lean_inc_ref(v_env_6699_);
                lean_dec(v___x_6698_);
                v___x_6700_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__2);
                lean_inc(v_mod_6689_);
                v_entry_6701_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v_entry_6701_, 0, v_mod_6689_);
                lean_ctor_set_uint8(
                    v_entry_6701_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_isExporting_6697_,
                );
                lean_ctor_set_uint8(
                    v_entry_6701_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v_isMeta_6690_,
                );
                v___x_6702_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_6703_ = lean_box(1);
                v___x_6704_ = lean_box(0);
                v___x_6732_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_6700_,
                    v___x_6702_,
                    v_env_6699_,
                    v___x_6703_,
                    v___x_6704_,
                );
                v___x_6733_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4_spec__15___redArg(v___x_6732_, v_entry_6701_);
                lean_dec(v___x_6732_);
                if v___x_6733_ == 0 {
                    v___x_6734_ = l_Lean_inheritedTraceOptions;
                    v___x_6735_ = lean_st_ref_get(v___x_6734_);
                    v___x_6736_ = lean_st_ref_get(v___y_6693_);
                    v_scopes_6737_ = lean_ctor_get(v___x_6736_, 2);
                    lean_inc(v_scopes_6737_);
                    lean_dec(v___x_6736_);
                    v___x_6738_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_6739_ = l_List_head_x21___redArg(v___x_6738_, v_scopes_6737_);
                    lean_dec(v_scopes_6737_);
                    v_opts_6740_ = lean_ctor_get(v___x_6739_, 1);
                    lean_inc_ref(v_opts_6740_);
                    lean_dec(v___x_6739_);
                    v_hasTrace_6741_ = lean_ctor_get_uint8(
                        v_opts_6740_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6741_ == 0 {
                        lean_dec_ref(v_opts_6740_);
                        lean_dec(v___x_6735_);
                        lean_dec(v_hint_6691_);
                        lean_dec(v_mod_6689_);
                        v___y_6706_ = v___y_6693_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_6742_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__8;
                        v___x_6762_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__14);
                        v___x_6763_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_6735_,
                            v_opts_6740_,
                            v___x_6762_,
                        );
                        lean_dec_ref(v_opts_6740_);
                        lean_dec(v___x_6735_);
                        if v___x_6763_ == 0 {
                            lean_dec(v_hint_6691_);
                            lean_dec(v_mod_6689_);
                            v___y_6706_ = v___y_6693_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6764_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__16);
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
                    lean_dec_ref_known(v_entry_6701_, 1);
                    lean_dec(v_hint_6691_);
                    lean_dec(v_mod_6689_);
                    v___x_6775_ = lean_box(0);
                    v___x_6776_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6776_, 0, v___x_6775_);
                    return v___x_6776_;
                }
            }
            1 => {
                v___x_6707_ = lean_st_ref_take(v___y_6706_);
                v_toEnvExtension_6708_ = lean_ctor_get(v___x_6702_, 0);
                v_env_6709_ = lean_ctor_get(v___x_6707_, 0);
                v_messages_6710_ = lean_ctor_get(v___x_6707_, 1);
                v_scopes_6711_ = lean_ctor_get(v___x_6707_, 2);
                v_usedQuotCtxts_6712_ = lean_ctor_get(v___x_6707_, 3);
                v_nextMacroScope_6713_ = lean_ctor_get(v___x_6707_, 4);
                v_maxRecDepth_6714_ = lean_ctor_get(v___x_6707_, 5);
                v_ngen_6715_ = lean_ctor_get(v___x_6707_, 6);
                v_auxDeclNGen_6716_ = lean_ctor_get(v___x_6707_, 7);
                v_infoState_6717_ = lean_ctor_get(v___x_6707_, 8);
                v_traceState_6718_ = lean_ctor_get(v___x_6707_, 9);
                v_snapshotTasks_6719_ = lean_ctor_get(v___x_6707_, 10);
                v_isSharedCheck_6731_ = (!lean_is_exclusive(v___x_6707_)) as u8;
                if v_isSharedCheck_6731_ == 0 {
                    v___x_6721_ = v___x_6707_;
                    v_isShared_6722_ = v_isSharedCheck_6731_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6719_);
                    lean_inc(v_traceState_6718_);
                    lean_inc(v_infoState_6717_);
                    lean_inc(v_auxDeclNGen_6716_);
                    lean_inc(v_ngen_6715_);
                    lean_inc(v_maxRecDepth_6714_);
                    lean_inc(v_nextMacroScope_6713_);
                    lean_inc(v_usedQuotCtxts_6712_);
                    lean_inc(v_scopes_6711_);
                    lean_inc(v_messages_6710_);
                    lean_inc(v_env_6709_);
                    lean_dec(v___x_6707_);
                    v___x_6721_ = lean_box(0);
                    v_isShared_6722_ = v_isSharedCheck_6731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_6723_ = lean_ctor_get(v_toEnvExtension_6708_, 2);
                v___x_6724_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6702_,
                    v_env_6709_,
                    v_entry_6701_,
                    v_asyncMode_6723_,
                    v___x_6704_,
                );
                if v_isShared_6722_ == 0 {
                    lean_ctor_set(v___x_6721_, 0, v___x_6724_);
                    v___x_6726_ = v___x_6721_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6730_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 0, v___x_6724_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 1, v_messages_6710_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 2, v_scopes_6711_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 3, v_usedQuotCtxts_6712_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 4, v_nextMacroScope_6713_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 5, v_maxRecDepth_6714_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 6, v_ngen_6715_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 7, v_auxDeclNGen_6716_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 8, v_infoState_6717_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 9, v_traceState_6718_);
                    lean_ctor_set(v_reuseFailAlloc_6730_, 10, v_snapshotTasks_6719_);
                    v___x_6726_ = v_reuseFailAlloc_6730_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6727_ = lean_st_ref_set(v___y_6706_, v___x_6726_);
                v___x_6728_ = lean_box(0);
                v___x_6729_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6729_, 0, v___x_6728_);
                return v___x_6729_;
            }
            4 => {
                v___x_6746_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6746_, 0, v___y_6744_);
                lean_ctor_set(v___x_6746_, 1, v___y_6745_);
                v___x_6747_ = l_Lean_addTrace___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1_spec__3(v_cls_6742_, v___x_6746_, v___y_6692_, v___y_6693_);
                if lean_obj_tag(v___x_6747_) == 0 {
                    lean_dec_ref_known(v___x_6747_, 1);
                    v___y_6706_ = v___y_6693_;
                    state = 1;
                    continue;
                } else {
                    lean_dec_ref_known(v_entry_6701_, 1);
                    return v___x_6747_;
                }
            }
            5 => {
                lean_inc_ref(v___y_6750_);
                v___x_6751_ = l_Lean_stringToMessageData(v___y_6750_);
                v___x_6752_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6752_, 0, v___y_6749_);
                lean_ctor_set(v___x_6752_, 1, v___x_6751_);
                v___x_6753_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__10);
                v___x_6754_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6754_, 0, v___x_6752_);
                lean_ctor_set(v___x_6754_, 1, v___x_6753_);
                v___x_6755_ = l_Lean_MessageData_ofName(v_mod_6689_);
                v___x_6756_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6756_, 0, v___x_6754_);
                lean_ctor_set(v___x_6756_, 1, v___x_6755_);
                v___x_6757_ = l_Lean_Name_isAnonymous(v_hint_6691_);
                if v___x_6757_ == 0 {
                    v___x_6758_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__12);
                    v___x_6759_ = l_Lean_MessageData_ofName(v_hint_6691_);
                    v___x_6760_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_6760_, 0, v___x_6758_);
                    lean_ctor_set(v___x_6760_, 1, v___x_6759_);
                    v___y_6744_ = v___x_6756_;
                    v___y_6745_ = v___x_6760_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_hint_6691_);
                    v___x_6761_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__13);
                    v___y_6744_ = v___x_6756_;
                    v___y_6745_ = v___x_6761_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v___y_6766_);
                v___x_6767_ = l_Lean_stringToMessageData(v___y_6766_);
                v___x_6768_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6768_, 0, v___x_6764_);
                lean_ctor_set(v___x_6768_, 1, v___x_6767_);
                v___x_6769_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2_spec__4___closed__18);
                v___x_6770_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_6770_, 0, v___x_6768_);
                lean_ctor_set(v___x_6770_, 1, v___x_6769_);
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
    mut v_mod_6777_: *mut LeanObject,
    mut v_isMeta_6778_: *mut LeanObject,
    mut v_hint_6779_: *mut LeanObject,
    mut v___y_6780_: *mut LeanObject,
    mut v___y_6781_: *mut LeanObject,
    mut v___y_6782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_6783_: u8 = 0;
    let mut v_res_6784_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6783_ = (lean_unbox(v_isMeta_6778_) as u8);
    v_res_6784_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_mod_6777_, v_isMeta_boxed_6783_, v_hint_6779_, v___y_6780_, v___y_6781_);
    lean_dec(v___y_6781_);
    lean_dec_ref(v___y_6780_);
    return v_res_6784_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(
    mut v___x_6785_: *mut LeanObject,
    mut v_declName_6786_: *mut LeanObject,
    mut v_as_6787_: *mut LeanObject,
    mut v_sz_6788_: usize,
    mut v_i_6789_: usize,
    mut v_b_6790_: *mut LeanObject,
    mut v___y_6791_: *mut LeanObject,
    mut v___y_6792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6794_: u8 = 0;
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toImport_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: u8 = 0;
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: usize = 0;
    let mut v___x_6807_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6794_ = lean_usize_dec_lt(v_i_6789_, v_sz_6788_);
                if v___x_6794_ == 0 {
                    lean_dec(v_declName_6786_);
                    v___x_6795_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6795_, 0, v_b_6790_);
                    return v___x_6795_;
                } else {
                    v___x_6796_ = l_Lean_Environment_header(v___x_6785_);
                    v_modules_6797_ = lean_ctor_get(v___x_6796_, 3);
                    lean_inc_ref(v_modules_6797_);
                    lean_dec_ref(v___x_6796_);
                    v___x_6798_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_6799_ = lean_array_uget_borrowed(v_as_6787_, v_i_6789_);
                    v___x_6800_ = lean_array_get(v___x_6798_, v_modules_6797_, v_a_6799_);
                    lean_dec_ref(v_modules_6797_);
                    v_toImport_6801_ = lean_ctor_get(v___x_6800_, 0);
                    lean_inc_ref(v_toImport_6801_);
                    lean_dec(v___x_6800_);
                    v_module_6802_ = lean_ctor_get(v_toImport_6801_, 0);
                    lean_inc(v_module_6802_);
                    lean_dec_ref(v_toImport_6801_);
                    v___x_6803_ = 0;
                    lean_inc(v_declName_6786_);
                    v___x_6804_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_6802_, v___x_6803_, v_declName_6786_, v___y_6791_, v___y_6792_);
                    if lean_obj_tag(v___x_6804_) == 0 {
                        lean_dec_ref_known(v___x_6804_, 1);
                        v___x_6805_ = lean_box(0);
                        v___x_6806_ = 1usize;
                        v___x_6807_ = lean_usize_add(v_i_6789_, v___x_6806_);
                        v_i_6789_ = v___x_6807_;
                        v_b_6790_ = v___x_6805_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_declName_6786_);
                        return v___x_6804_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2___boxed(
    mut v___x_6809_: *mut LeanObject,
    mut v_declName_6810_: *mut LeanObject,
    mut v_as_6811_: *mut LeanObject,
    mut v_sz_6812_: *mut LeanObject,
    mut v_i_6813_: *mut LeanObject,
    mut v_b_6814_: *mut LeanObject,
    mut v___y_6815_: *mut LeanObject,
    mut v___y_6816_: *mut LeanObject,
    mut v___y_6817_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6818_: usize = 0;
    let mut v_i_boxed_6819_: usize = 0;
    let mut v_res_6820_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6818_ = lean_unbox_usize(v_sz_6812_);
    lean_dec(v_sz_6812_);
    v_i_boxed_6819_ = lean_unbox_usize(v_i_6813_);
    lean_dec(v_i_6813_);
    v_res_6820_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v___x_6809_, v_declName_6810_, v_as_6811_, v_sz_boxed_6818_, v_i_boxed_6819_, v_b_6814_, v___y_6815_, v___y_6816_);
    lean_dec(v___y_6816_);
    lean_dec_ref(v___y_6815_);
    lean_dec_ref(v_as_6811_);
    lean_dec_ref(v___x_6809_);
    return v_res_6820_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(
    mut v_declName_6821_: *mut LeanObject,
    mut v_isMeta_6822_: u8,
    mut v___y_6823_: *mut LeanObject,
    mut v___y_6824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6834_: usize = 0;
    let mut v___x_6835_: usize = 0;
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6839_: u8 = 0;
    let mut v___x_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6843_: u8 = 0;
    let mut v_unused_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modules_6848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: u8 = 0;
    let mut v___x_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6856_: u8 = 0;
    let mut v_toImport_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_module_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: u8 = 0;
    let mut v___x_6868_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6826_ = lean_st_ref_get(v___y_6824_);
                v_env_6830_ = lean_ctor_get(v___x_6826_, 0);
                lean_inc_ref(v_env_6830_);
                lean_dec(v___x_6826_);
                v___x_6845_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6830_, v_declName_6821_);
                if lean_obj_tag(v___x_6845_) == 0 {
                    lean_dec_ref(v_env_6830_);
                    lean_dec(v_declName_6821_);
                    state = 1;
                    continue;
                } else {
                    v_val_6846_ = lean_ctor_get(v___x_6845_, 0);
                    lean_inc(v_val_6846_);
                    lean_dec_ref_known(v___x_6845_, 1);
                    v___x_6847_ = l_Lean_Environment_header(v_env_6830_);
                    v_modules_6848_ = lean_ctor_get(v___x_6847_, 3);
                    lean_inc_ref(v_modules_6848_);
                    lean_dec_ref(v___x_6847_);
                    v___x_6849_ = lean_array_get_size(v_modules_6848_);
                    v___x_6850_ = lean_nat_dec_lt(v_val_6846_, v___x_6849_);
                    if v___x_6850_ == 0 {
                        lean_dec_ref(v_modules_6848_);
                        lean_dec(v_val_6846_);
                        lean_dec_ref(v_env_6830_);
                        lean_dec(v_declName_6821_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6851_ = lean_st_ref_get(v___y_6824_);
                        v_env_6852_ = lean_ctor_get(v___x_6851_, 0);
                        lean_inc_ref(v_env_6852_);
                        lean_dec(v___x_6851_);
                        v___x_6853_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__2);
                        v___x_6854_ = lean_array_fget(v_modules_6848_, v_val_6846_);
                        lean_dec(v_val_6846_);
                        lean_dec_ref(v_modules_6848_);
                        if v_isMeta_6822_ == 0 {
                            lean_dec_ref(v_env_6852_);
                            v___y_6856_ = v_isMeta_6822_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_declName_6821_);
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
                v___x_6828_ = lean_box(0);
                v___x_6829_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6829_, 0, v___x_6828_);
                return v___x_6829_;
            }
            2 => {
                v___x_6833_ = lean_box(0);
                v_sz_6834_ = lean_array_size(v___y_6832_);
                v___x_6835_ = 0usize;
                v___x_6836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__2(v_env_6830_, v_declName_6821_, v___y_6832_, v_sz_6834_, v___x_6835_, v___x_6833_, v___y_6823_, v___y_6824_);
                lean_dec_ref(v___y_6832_);
                lean_dec_ref(v_env_6830_);
                if lean_obj_tag(v___x_6836_) == 0 {
                    v_isSharedCheck_6843_ = (!lean_is_exclusive(v___x_6836_)) as u8;
                    if v_isSharedCheck_6843_ == 0 {
                        v_unused_6844_ = lean_ctor_get(v___x_6836_, 0);
                        lean_dec(v_unused_6844_);
                        v___x_6838_ = v___x_6836_;
                        v_isShared_6839_ = v_isSharedCheck_6843_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_6836_);
                        v___x_6838_ = lean_box(0);
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
                    lean_ctor_set(v___x_6838_, 0, v___x_6833_);
                    v___x_6841_ = v___x_6838_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6842_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6842_, 0, v___x_6833_);
                    v___x_6841_ = v_reuseFailAlloc_6842_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6841_;
            }
            5 => {
                v_toImport_6857_ = lean_ctor_get(v___x_6854_, 0);
                lean_inc_ref(v_toImport_6857_);
                lean_dec(v___x_6854_);
                v_module_6858_ = lean_ctor_get(v_toImport_6857_, 0);
                lean_inc(v_module_6858_);
                lean_dec_ref(v_toImport_6857_);
                lean_inc(v_declName_6821_);
                v___x_6859_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1_spec__1(v_module_6858_, v___y_6856_, v_declName_6821_, v___y_6823_, v___y_6824_);
                if lean_obj_tag(v___x_6859_) == 0 {
                    lean_dec_ref_known(v___x_6859_, 1);
                    v___x_6860_ = l_Lean_indirectModUseExt;
                    v___x_6861_ = lean_box(1);
                    v___x_6862_ = lean_box(0);
                    lean_inc_ref(v_env_6830_);
                    v___x_6863_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_6853_,
                        v___x_6860_,
                        v_env_6830_,
                        v___x_6861_,
                        v___x_6862_,
                    );
                    v___x_6864_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__6___redArg(v___x_6863_, v_declName_6821_);
                    lean_dec(v___x_6863_);
                    if lean_obj_tag(v___x_6864_) == 0 {
                        v___x_6865_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__2___closed__3;
                        v___y_6832_ = v___x_6865_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6866_ = lean_ctor_get(v___x_6864_, 0);
                        lean_inc(v_val_6866_);
                        lean_dec_ref_known(v___x_6864_, 1);
                        v___y_6832_ = v_val_6866_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_env_6830_);
                    lean_dec(v_declName_6821_);
                    return v___x_6859_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1___boxed(
    mut v_declName_6869_: *mut LeanObject,
    mut v_isMeta_6870_: *mut LeanObject,
    mut v___y_6871_: *mut LeanObject,
    mut v___y_6872_: *mut LeanObject,
    mut v___y_6873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isMeta_boxed_6874_: u8 = 0;
    let mut v_res_6875_: *mut LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6874_ = (lean_unbox(v_isMeta_6870_) as u8);
    v_res_6875_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v_declName_6869_, v_isMeta_boxed_6874_, v___y_6871_, v___y_6872_);
    lean_dec(v___y_6872_);
    lean_dec_ref(v___y_6871_);
    return v_res_6875_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4()
-> *mut LeanObject {
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut LeanObject = core::ptr::null_mut();
    v___x_6884_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__3;
    v___x_6885_ = l_Lean_stringToMessageData(v___x_6884_);
    return v___x_6885_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5()
-> *mut LeanObject {
    let mut v___x_6886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    v___x_6886_ = l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__28;
    v___x_6887_ = l_Lean_stringToMessageData(v___x_6886_);
    return v___x_6887_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7()
-> *mut LeanObject {
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut LeanObject = core::ptr::null_mut();
    v___x_6889_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__6;
    v___x_6890_ = l_Lean_stringToMessageData(v___x_6889_);
    return v___x_6890_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9()
-> *mut LeanObject {
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut LeanObject = core::ptr::null_mut();
    v___x_6892_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__8;
    v___x_6893_ = l_Lean_stringToMessageData(v___x_6892_);
    return v___x_6893_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__11()
-> *mut LeanObject {
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut LeanObject = core::ptr::null_mut();
    v___x_6895_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__10;
    v___x_6896_ = l_Lean_stringToMessageData(v___x_6895_);
    return v___x_6896_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12()
-> *mut LeanObject {
    let mut v___x_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6898_: *mut LeanObject = core::ptr::null_mut();
    v___x_6897_ = lean_obj_once(
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
-> *mut LeanObject {
    let mut v___x_6900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut LeanObject = core::ptr::null_mut();
    v___x_6900_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__13;
    v___x_6901_ = l_Lean_stringToMessageData(v___x_6900_);
    return v___x_6901_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17()
-> *mut LeanObject {
    let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    v___x_6907_ = lean_box(0);
    v___x_6908_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
    v___x_6909_ = l_Lean_mkConst(v___x_6908_, v___x_6907_);
    return v___x_6909_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19()
-> *mut LeanObject {
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6912_: *mut LeanObject = core::ptr::null_mut();
    v___x_6911_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__18;
    v___x_6912_ = l_Lean_stringToMessageData(v___x_6911_);
    return v___x_6912_;
}
pub unsafe fn _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21()
-> *mut LeanObject {
    let mut v___x_6914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut LeanObject = core::ptr::null_mut();
    v___x_6914_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__20;
    v___x_6915_ = l_Lean_stringToMessageData(v___x_6914_);
    return v___x_6915_;
}
pub unsafe fn l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(
    mut v_x_6916_: *mut LeanObject,
    mut v_a_6917_: *mut LeanObject,
    mut v_a_6918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6932_: u8 = 0;
    let mut v___x_6933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_6935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_6936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_6940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6947_: u8 = 0;
    let mut v___x_6948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6967_: u8 = 0;
    let mut v_isSharedCheck_6968_: u8 = 0;
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: u8 = 0;
    let mut v___x_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6981_: u8 = 0;
    let mut v___y_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: u8 = 0;
    let mut v___x_6996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_7004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7011_: u8 = 0;
    let mut v___x_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: u8 = 0;
    let mut v___y_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: u8 = 0;
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: u8 = 0;
    let mut v___x_7041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_7051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_7054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_macroStack_7055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_7056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7060_: u8 = 0;
    let mut v_env_7061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cmd_7062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_t_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7075_: u8 = 0;
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7085_: u8 = 0;
    let mut v___x_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7089_: u8 = 0;
    let mut v_ref_7090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7093_: u8 = 0;
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7099_: u8 = 0;
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6969_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
                lean_inc(v_x_6916_);
                v___x_6970_ = l_Lean_Syntax_isOfKind(v_x_6916_, v___x_6969_);
                if v___x_6970_ == 0 {
                    lean_dec(v_x_6916_);
                    v___x_6971_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
                    return v___x_6971_;
                } else {
                    v___x_6972_ = lean_unsigned_to_nat(0);
                    v___x_6973_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_6972_);
                    v___x_6974_ = lean_unsigned_to_nat(1);
                    v___x_6975_ = l_Lean_Syntax_matchesNull(v___x_6973_, v___x_6974_);
                    if v___x_6975_ == 0 {
                        lean_dec(v_x_6916_);
                        v___x_6976_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
                        return v___x_6976_;
                    } else {
                        v___x_6977_ = lean_unsigned_to_nat(2);
                        v_id_6978_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_6977_);
                        v___x_7018_ =
                            l_Lean_Elab_ErrorExplanation_expandNamedErrorMacro___closed__58;
                        lean_inc(v_id_6978_);
                        v___x_7019_ = l_Lean_Syntax_isOfKind(v_id_6978_, v___x_7018_);
                        if v___x_7019_ == 0 {
                            lean_dec(v_id_6978_);
                            lean_dec(v_x_6916_);
                            v___x_7047_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__0___redArg();
                            return v___x_7047_;
                        } else {
                            v___x_7048_ = l_Lean_Elab_Command_getRef___redArg(v_a_6917_);
                            if lean_obj_tag(v___x_7048_) == 0 {
                                v_a_7049_ = lean_ctor_get(v___x_7048_, 0);
                                lean_inc(v_a_7049_);
                                lean_dec_ref_known(v___x_7048_, 1);
                                v___x_7050_ = lean_st_ref_get(v_a_6918_);
                                v_fileName_7051_ = lean_ctor_get(v_a_6917_, 0);
                                v_fileMap_7052_ = lean_ctor_get(v_a_6917_, 1);
                                v_currRecDepth_7053_ = lean_ctor_get(v_a_6917_, 2);
                                v_cmdPos_7054_ = lean_ctor_get(v_a_6917_, 3);
                                v_macroStack_7055_ = lean_ctor_get(v_a_6917_, 4);
                                v_quotContext_x3f_7056_ = lean_ctor_get(v_a_6917_, 5);
                                v_currMacroScope_7057_ = lean_ctor_get(v_a_6917_, 6);
                                v_snap_x3f_7058_ = lean_ctor_get(v_a_6917_, 8);
                                v_cancelTk_x3f_7059_ = lean_ctor_get(v_a_6917_, 9);
                                v_suppressElabErrors_7060_ = lean_ctor_get_uint8(
                                    v_a_6917_,
                                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                                );
                                v_env_7061_ = lean_ctor_get(v___x_7050_, 0);
                                lean_inc_ref(v_env_7061_);
                                lean_dec(v___x_7050_);
                                v_cmd_7062_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_6974_);
                                v___x_7063_ = lean_unsigned_to_nat(3);
                                v_t_7064_ = l_Lean_Syntax_getArg(v_x_6916_, v___x_7063_);
                                lean_dec(v_x_6916_);
                                v_ref_7090_ = l_Lean_replaceRef(v_cmd_7062_, v_a_7049_);
                                lean_dec(v_a_7049_);
                                lean_dec(v_cmd_7062_);
                                lean_inc(v_cancelTk_x3f_7059_);
                                lean_inc(v_snap_x3f_7058_);
                                lean_inc(v_currMacroScope_7057_);
                                lean_inc(v_quotContext_x3f_7056_);
                                lean_inc(v_macroStack_7055_);
                                lean_inc(v_cmdPos_7054_);
                                lean_inc(v_currRecDepth_7053_);
                                lean_inc_ref(v_fileMap_7052_);
                                lean_inc_ref(v_fileName_7051_);
                                v___x_7091_ = lean_alloc_ctor(0, 10, (1) as u32);
                                lean_ctor_set(v___x_7091_, 0, v_fileName_7051_);
                                lean_ctor_set(v___x_7091_, 1, v_fileMap_7052_);
                                lean_ctor_set(v___x_7091_, 2, v_currRecDepth_7053_);
                                lean_ctor_set(v___x_7091_, 3, v_cmdPos_7054_);
                                lean_ctor_set(v___x_7091_, 4, v_macroStack_7055_);
                                lean_ctor_set(v___x_7091_, 5, v_quotContext_x3f_7056_);
                                lean_ctor_set(v___x_7091_, 6, v_currMacroScope_7057_);
                                lean_ctor_set(v___x_7091_, 7, v_ref_7090_);
                                lean_ctor_set(v___x_7091_, 8, v_snap_x3f_7058_);
                                lean_ctor_set(v___x_7091_, 9, v_cancelTk_x3f_7059_);
                                lean_ctor_set_uint8(
                                    v___x_7091_,
                                    (core::mem::size_of::<*mut LeanObject>() * 10) as u32,
                                    v_suppressElabErrors_7060_,
                                );
                                v___x_7092_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
                                v___x_7093_ = l_Lean_Environment_contains(
                                    v_env_7061_,
                                    v___x_7092_,
                                    v___x_7019_,
                                );
                                if v___x_7093_ == 0 {
                                    lean_dec(v_t_7064_);
                                    lean_dec(v_id_6978_);
                                    v___x_7094_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__21);
                                    v___x_7095_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v___x_7094_, v___x_7091_, v_a_6918_);
                                    lean_dec_ref_known(v___x_7091_, 10);
                                    return v___x_7095_;
                                } else {
                                    v___y_7066_ = v___x_7091_;
                                    v___y_7067_ = v_a_6918_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                lean_dec(v_id_6978_);
                                lean_dec(v_x_6916_);
                                v_a_7096_ = lean_ctor_get(v___x_7048_, 0);
                                v_isSharedCheck_7103_ = (!lean_is_exclusive(v___x_7048_)) as u8;
                                if v_isSharedCheck_7103_ == 0 {
                                    v___x_7098_ = v___x_7048_;
                                    v_isShared_7099_ = v_isSharedCheck_7103_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_a_7096_);
                                    lean_dec(v___x_7048_);
                                    v___x_7098_ = lean_box(0);
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
                lean_dec_ref(v___y_6925_);
                v___x_6928_ = l_Lean_getMainModule___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__2___redArg(v___y_6926_);
                v_a_6929_ = lean_ctor_get(v___x_6928_, 0);
                v_isSharedCheck_6968_ = (!lean_is_exclusive(v___x_6928_)) as u8;
                if v_isSharedCheck_6968_ == 0 {
                    v___x_6931_ = v___x_6928_;
                    v_isShared_6932_ = v_isSharedCheck_6968_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_6929_);
                    lean_dec(v___x_6928_);
                    v___x_6931_ = lean_box(0);
                    v_isShared_6932_ = v_isSharedCheck_6968_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6933_ = lean_st_ref_take(v___y_6926_);
                v_env_6934_ = lean_ctor_get(v___x_6933_, 0);
                v_messages_6935_ = lean_ctor_get(v___x_6933_, 1);
                v_scopes_6936_ = lean_ctor_get(v___x_6933_, 2);
                v_usedQuotCtxts_6937_ = lean_ctor_get(v___x_6933_, 3);
                v_nextMacroScope_6938_ = lean_ctor_get(v___x_6933_, 4);
                v_maxRecDepth_6939_ = lean_ctor_get(v___x_6933_, 5);
                v_ngen_6940_ = lean_ctor_get(v___x_6933_, 6);
                v_auxDeclNGen_6941_ = lean_ctor_get(v___x_6933_, 7);
                v_infoState_6942_ = lean_ctor_get(v___x_6933_, 8);
                v_traceState_6943_ = lean_ctor_get(v___x_6933_, 9);
                v_snapshotTasks_6944_ = lean_ctor_get(v___x_6933_, 10);
                v_isSharedCheck_6967_ = (!lean_is_exclusive(v___x_6933_)) as u8;
                if v_isSharedCheck_6967_ == 0 {
                    v___x_6946_ = v___x_6933_;
                    v_isShared_6947_ = v_isSharedCheck_6967_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_6944_);
                    lean_inc(v_traceState_6943_);
                    lean_inc(v_infoState_6942_);
                    lean_inc(v_auxDeclNGen_6941_);
                    lean_inc(v_ngen_6940_);
                    lean_inc(v_maxRecDepth_6939_);
                    lean_inc(v_nextMacroScope_6938_);
                    lean_inc(v_usedQuotCtxts_6937_);
                    lean_inc(v_scopes_6936_);
                    lean_inc(v_messages_6935_);
                    lean_inc(v_env_6934_);
                    lean_dec(v___x_6933_);
                    v___x_6946_ = lean_box(0);
                    v_isShared_6947_ = v_isSharedCheck_6967_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6948_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_6949_ = lean_ctor_get(v___x_6948_, 0);
                v_asyncMode_6950_ = lean_ctor_get(v_toEnvExtension_6949_, 2);
                v___x_6951_ = l_Lean_DeclarationRange_ofStringPositions(
                    v___y_6921_,
                    v___y_6923_,
                    v___y_6927_,
                );
                lean_dec(v___y_6927_);
                lean_dec(v___y_6923_);
                v___x_6952_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6952_, 0, v_a_6929_);
                lean_ctor_set(v___x_6952_, 1, v___x_6951_);
                v___x_6953_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6953_, 0, v___x_6952_);
                v___x_6954_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_ErrorExplanation_elabCheckedNamedError_spec__0_spec__0___redArg___closed__1;
                v___x_6955_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_6955_, 0, v___x_6954_);
                lean_ctor_set(v___x_6955_, 1, v___y_6922_);
                lean_ctor_set(v___x_6955_, 2, v___x_6953_);
                v___x_6956_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6956_, 0, v___y_6924_);
                lean_ctor_set(v___x_6956_, 1, v___x_6955_);
                v___x_6957_ = lean_box(0);
                v___x_6958_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6948_,
                    v_env_6934_,
                    v___x_6956_,
                    v_asyncMode_6950_,
                    v___x_6957_,
                );
                if v_isShared_6947_ == 0 {
                    lean_ctor_set(v___x_6946_, 0, v___x_6958_);
                    v___x_6960_ = v___x_6946_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6966_ = lean_alloc_ctor(0, 11, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 0, v___x_6958_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 1, v_messages_6935_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 2, v_scopes_6936_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 3, v_usedQuotCtxts_6937_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 4, v_nextMacroScope_6938_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 5, v_maxRecDepth_6939_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 6, v_ngen_6940_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 7, v_auxDeclNGen_6941_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 8, v_infoState_6942_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 9, v_traceState_6943_);
                    lean_ctor_set(v_reuseFailAlloc_6966_, 10, v_snapshotTasks_6944_);
                    v___x_6960_ = v_reuseFailAlloc_6966_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6961_ = lean_st_ref_set(v___y_6926_, v___x_6960_);
                v___x_6962_ = lean_box(0);
                if v_isShared_6932_ == 0 {
                    lean_ctor_set(v___x_6931_, 0, v___x_6962_);
                    v___x_6964_ = v___x_6931_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6965_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6965_, 0, v___x_6962_);
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
                lean_dec(v_id_6978_);
                if lean_obj_tag(v___x_6987_) == 0 {
                    lean_inc(v___y_6986_);
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
                    v_val_6988_ = lean_ctor_get(v___x_6987_, 0);
                    lean_inc(v_val_6988_);
                    lean_dec_ref_known(v___x_6987_, 1);
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
                v_fileMap_6994_ = lean_ctor_get(v___y_6992_, 1);
                lean_inc_ref(v_fileMap_6994_);
                v___x_6995_ = 0;
                v___x_6996_ = l_Lean_Syntax_getPos_x3f(v_id_6978_, v___x_6995_);
                if lean_obj_tag(v___x_6996_) == 0 {
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
                    v_val_6997_ = lean_ctor_get(v___x_6996_, 0);
                    lean_inc(v_val_6997_);
                    lean_dec_ref_known(v___x_6996_, 1);
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
                v_env_7004_ = lean_ctor_get(v___x_7003_, 0);
                lean_inc_ref(v_env_7004_);
                lean_dec(v___x_7003_);
                v___x_7005_ = l_Lean_errorExplanationExt;
                v_toEnvExtension_7006_ = lean_ctor_get(v___x_7005_, 0);
                v_asyncMode_7007_ = lean_ctor_get(v_toEnvExtension_7006_, 2);
                v___x_7008_ = lean_box(1);
                v___x_7009_ = lean_box(0);
                v___x_7010_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_7008_,
                    v___x_7005_,
                    v_env_7004_,
                    v_asyncMode_7007_,
                    v___x_7009_,
                );
                v___x_7011_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v___y_7000_, v___x_7010_);
                lean_dec(v___x_7010_);
                if v___x_7011_ == 0 {
                    v___y_6990_ = v___y_6999_;
                    v___y_6991_ = v___y_7000_;
                    v___y_6992_ = v___y_7001_;
                    v___y_6993_ = v___y_7002_;
                    state = 7;
                    continue;
                } else {
                    lean_dec_ref(v___y_6999_);
                    v___x_7012_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__4);
                    v___x_7013_ = l_Lean_MessageData_ofName(v___y_7000_);
                    v___x_7014_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7014_, 0, v___x_7012_);
                    lean_ctor_set(v___x_7014_, 1, v___x_7013_);
                    v___x_7015_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
                    v___x_7016_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7016_, 0, v___x_7014_);
                    lean_ctor_set(v___x_7016_, 1, v___x_7015_);
                    v___x_7017_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7016_, v___y_7001_, v___y_7002_);
                    lean_dec_ref(v___y_7001_);
                    lean_dec(v_id_6978_);
                    return v___x_7017_;
                }
            }
            9 => {
                v___x_7025_ = l_Lean_Name_getNumParts(v___y_7022_);
                v___x_7026_ = lean_nat_dec_eq(v___x_7025_, v___x_6977_);
                lean_dec(v___x_7025_);
                if v___x_7026_ == 0 {
                    if v___x_7019_ == 0 {
                        v___y_6999_ = v___y_7021_;
                        v___y_7000_ = v___y_7022_;
                        v___y_7001_ = v___y_7023_;
                        v___y_7002_ = v___y_7024_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec_ref(v___y_7021_);
                        v___x_7027_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
                        v___x_7028_ = l_Lean_MessageData_ofName(v___y_7022_);
                        v___x_7029_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7029_, 0, v___x_7027_);
                        lean_ctor_set(v___x_7029_, 1, v___x_7028_);
                        v___x_7030_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__9);
                        v___x_7031_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7031_, 0, v___x_7029_);
                        lean_ctor_set(v___x_7031_, 1, v___x_7030_);
                        v___x_7032_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__12);
                        v___x_7033_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_7033_, 0, v___x_7031_);
                        lean_ctor_set(v___x_7033_, 1, v___x_7032_);
                        v___x_7034_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7033_, v___y_7023_, v___y_7024_);
                        lean_dec_ref(v___y_7023_);
                        lean_dec(v_id_6978_);
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
                    lean_dec(v___y_7037_);
                    lean_dec_ref(v___y_7036_);
                    v___x_7041_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__7);
                    lean_inc(v_id_6978_);
                    v___x_7042_ = l_Lean_MessageData_ofSyntax(v_id_6978_);
                    v___x_7043_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7043_, 0, v___x_7041_);
                    lean_ctor_set(v___x_7043_, 1, v___x_7042_);
                    v___x_7044_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__14);
                    v___x_7045_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_7045_, 0, v___x_7043_);
                    lean_ctor_set(v___x_7045_, 1, v___x_7044_);
                    v___x_7046_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7045_, v___y_7038_, v___y_7039_);
                    lean_dec_ref(v___y_7038_);
                    lean_dec(v_id_6978_);
                    return v___x_7046_;
                }
            }
            11 => {
                v___x_7068_ =
                    l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__16;
                v___x_7069_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__1(v___x_7068_, v___x_7019_, v___y_7066_, v___y_7067_);
                if lean_obj_tag(v___x_7069_) == 0 {
                    lean_dec_ref_known(v___x_7069_, 1);
                    v___x_7070_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__17);
                    v___f_7071_ = lean_alloc_closure(
                        l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___lam__0___boxed
                            as *mut core::ffi::c_void,
                        10,
                        2,
                    );
                    lean_closure_set(v___f_7071_, 0, v_t_7064_);
                    lean_closure_set(v___f_7071_, 1, v___x_7070_);
                    v___x_7072_ = l_Lean_Elab_Command_runTermElabM___redArg(
                        v___f_7071_,
                        v___y_7066_,
                        v___y_7067_,
                    );
                    if lean_obj_tag(v___x_7072_) == 0 {
                        v_a_7073_ = lean_ctor_get(v___x_7072_, 0);
                        lean_inc(v_a_7073_);
                        lean_dec_ref_known(v___x_7072_, 1);
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
                            lean_dec(v___x_7074_);
                            lean_dec(v_a_7073_);
                            v___x_7076_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__19);
                            lean_inc(v_id_6978_);
                            v___x_7077_ = l_Lean_MessageData_ofSyntax(v_id_6978_);
                            v___x_7078_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_7078_, 0, v___x_7076_);
                            lean_ctor_set(v___x_7078_, 1, v___x_7077_);
                            v___x_7079_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5_once), _init_l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__5);
                            v___x_7080_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_7080_, 0, v___x_7078_);
                            lean_ctor_set(v___x_7080_, 1, v___x_7079_);
                            v___x_7081_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_id_6978_, v___x_7080_, v___y_7066_, v___y_7067_);
                            lean_dec_ref(v___y_7066_);
                            lean_dec(v_id_6978_);
                            return v___x_7081_;
                        }
                    } else {
                        lean_dec_ref(v___y_7066_);
                        lean_dec(v_id_6978_);
                        v_a_7082_ = lean_ctor_get(v___x_7072_, 0);
                        v_isSharedCheck_7089_ = (!lean_is_exclusive(v___x_7072_)) as u8;
                        if v_isSharedCheck_7089_ == 0 {
                            v___x_7084_ = v___x_7072_;
                            v_isShared_7085_ = v_isSharedCheck_7089_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_7082_);
                            lean_dec(v___x_7072_);
                            v___x_7084_ = lean_box(0);
                            v_isShared_7085_ = v_isSharedCheck_7089_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_7066_);
                    lean_dec(v_t_7064_);
                    lean_dec(v_id_6978_);
                    return v___x_7069_;
                }
            }
            12 => {
                if v_isShared_7085_ == 0 {
                    v___x_7087_ = v___x_7084_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7088_, 0, v_a_7082_);
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
                    v_reuseFailAlloc_7102_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7102_, 0, v_a_7096_);
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
    mut v_x_7104_: *mut LeanObject,
    mut v_a_7105_: *mut LeanObject,
    mut v_a_7106_: *mut LeanObject,
    mut v_a_7107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7108_: *mut LeanObject = core::ptr::null_mut();
    v_res_7108_ =
        l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation(v_x_7104_, v_a_7105_, v_a_7106_);
    lean_dec(v_a_7106_);
    lean_dec_ref(v_a_7105_);
    return v_res_7108_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(
    mut v_00_u03b1_7109_: *mut LeanObject,
    mut v_ref_7110_: *mut LeanObject,
    mut v_msg_7111_: *mut LeanObject,
    mut v___y_7112_: *mut LeanObject,
    mut v___y_7113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    v___x_7115_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___redArg(v_ref_7110_, v_msg_7111_, v___y_7112_, v___y_7113_);
    return v___x_7115_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3___boxed(
    mut v_00_u03b1_7116_: *mut LeanObject,
    mut v_ref_7117_: *mut LeanObject,
    mut v_msg_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
    mut v___y_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7122_: *mut LeanObject = core::ptr::null_mut();
    v_res_7122_ = l_Lean_throwErrorAt___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__3(v_00_u03b1_7116_, v_ref_7117_, v_msg_7118_, v___y_7119_, v___y_7120_);
    lean_dec(v___y_7120_);
    lean_dec_ref(v___y_7119_);
    lean_dec(v_ref_7117_);
    return v_res_7122_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(
    mut v_msgData_7123_: *mut LeanObject,
    mut v___y_7124_: *mut LeanObject,
    mut v___y_7125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    v___x_7127_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___redArg(v_msgData_7123_, v___y_7125_);
    return v___x_7127_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6___boxed(
    mut v_msgData_7128_: *mut LeanObject,
    mut v___y_7129_: *mut LeanObject,
    mut v___y_7130_: *mut LeanObject,
    mut v___y_7131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7132_: *mut LeanObject = core::ptr::null_mut();
    v_res_7132_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__6(v_msgData_7128_, v___y_7129_, v___y_7130_);
    lean_dec(v___y_7130_);
    lean_dec_ref(v___y_7129_);
    return v_res_7132_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(
    mut v_00_u03b1_7133_: *mut LeanObject,
    mut v_msg_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
    mut v___y_7136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    v___x_7138_ = l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___redArg(v_msg_7134_, v___y_7135_, v___y_7136_);
    return v___x_7138_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4___boxed(
    mut v_00_u03b1_7139_: *mut LeanObject,
    mut v_msg_7140_: *mut LeanObject,
    mut v___y_7141_: *mut LeanObject,
    mut v___y_7142_: *mut LeanObject,
    mut v___y_7143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7144_: *mut LeanObject = core::ptr::null_mut();
    v_res_7144_ =
        l_Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4(
            v_00_u03b1_7139_,
            v_msg_7140_,
            v___y_7141_,
            v___y_7142_,
        );
    lean_dec(v___y_7142_);
    lean_dec_ref(v___y_7141_);
    return v_res_7144_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(
    mut v_msgData_7145_: *mut LeanObject,
    mut v_macroStack_7146_: *mut LeanObject,
    mut v___y_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7150_: *mut LeanObject = core::ptr::null_mut();
    v___x_7150_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___redArg(v_msgData_7145_, v_macroStack_7146_, v___y_7148_);
    return v___x_7150_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7___boxed(
    mut v_msgData_7151_: *mut LeanObject,
    mut v_macroStack_7152_: *mut LeanObject,
    mut v___y_7153_: *mut LeanObject,
    mut v___y_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7156_: *mut LeanObject = core::ptr::null_mut();
    v_res_7156_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation_spec__4_spec__7(v_msgData_7151_, v_macroStack_7152_, v___y_7153_, v___y_7154_);
    lean_dec(v___y_7154_);
    lean_dec_ref(v___y_7153_);
    return v_res_7156_;
}
pub unsafe fn l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1()
-> *mut LeanObject {
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7168_: *mut LeanObject = core::ptr::null_mut();
    v___x_7164_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_7165_ = l_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___closed__2;
    v___x_7166_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1___closed__1;
    v___x_7167_ = lean_alloc_closure(
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
    mut v_a_7169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7170_: *mut LeanObject = core::ptr::null_mut();
    v_res_7170_ = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
    return v_res_7170_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ErrorExplanation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_errorDescriptionWidget___regBuiltin_Lean_errorDescriptionWidget__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap =
        _init_l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap();
    lean_mark_persistent(
        l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_macroDeclMap,
    );
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__5();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__7();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__9();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabCheckedNamedError___regBuiltin_Lean_Elab_ErrorExplanation_elabCheckedNamedError__11();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_ErrorExplanation_0__Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation___regBuiltin_Lean_Elab_ErrorExplanation_elabRegisterErrorExplanation__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ErrorExplanation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ErrorExplanation(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Widget_UserWidget(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ErrorExplanation(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_ErrorExplanation(builtin);
}
