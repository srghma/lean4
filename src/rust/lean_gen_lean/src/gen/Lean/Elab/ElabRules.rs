// Lean compiler output
// Module: Lean.Elab.ElabRules
// Imports: Lean.Elab.MacroArgUtil Lean.Elab.AuxDef Lean.Elab.Do.Basic
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_unzip___redArg};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::BasicAux::l_List_head_x21___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Meta::Defs::{
    l_Lean_Syntax_SepArray_ofElems, l_Lean_Syntax_TSepArray_getElems___redArg,
    l_Lean_Syntax_isNone, l_Lean_Syntax_mkNumLit, l_Lean_TSyntax_getId, l_Lean_evalOptPrio___boxed,
    l_Lean_mkIdentFrom, lean_mk_syntax_ident,
};
use crate::r#gen::Init::Prelude::{
    l_Array_mkArray0, l_Array_mkArray1___redArg, l_Array_mkArray2___redArg,
    l_Array_mkArray5___redArg, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
    l_Lean_SourceInfo_fromRef, l_Lean_Syntax_getArg, l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind,
    l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesNull, l_Lean_Syntax_node1, l_Lean_Syntax_node2,
    l_Lean_Syntax_node3, l_Lean_Syntax_node4, l_Lean_Syntax_node5, l_Lean_Syntax_node6,
    l_Lean_Syntax_node8, l_Lean_addMacroScope, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
    l_String_toRawSubstring_x27,
};
use crate::r#gen::Init::Syntax::l_Lean_Syntax_setArg;
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::Elab::AuxDef::{
    initialize_Lean_Elab_AuxDef, runtime_initialize_Lean_Elab_AuxDef,
};
use crate::r#gen::Lean::Elab::Command::Scope::l_Lean_Elab_Command_instInhabitedScope_default;
use crate::r#gen::Lean::Elab::Command::{
    l_Lean_Elab_Command_adaptExpander, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_elabCommand, l_Lean_Elab_Command_getCurrMacroScope___redArg,
    l_Lean_Elab_Command_getRef___redArg, l_Lean_Elab_Command_getScope___redArg,
    l_Lean_Parser_Command_visibility_ofAttrKind,
};
use crate::r#gen::Lean::Elab::Do::Basic::{
    initialize_Lean_Elab_Do_Basic, runtime_initialize_Lean_Elab_Do_Basic,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::MacroArgUtil::{
    initialize_Lean_Elab_MacroArgUtil, l_Lean_Elab_Command_expandMacroArg,
    runtime_initialize_Lean_Elab_MacroArgUtil,
};
use crate::r#gen::Lean::Elab::Syntax::{
    l_Lean_Elab_Command_checkRuleKind, l_Lean_Elab_Command_elabSyntax,
    l_Lean_Elab_Command_expandNoKindMacroRulesAux, l_Lean_Elab_Command_resolveSyntaxKind,
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
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_getQuotContent, l_Lean_Syntax_isQuot};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_inheritedTraceOptions,
};
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
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
    lean_nat_add, lean_nat_dec_lt, lean_string_dec_eq, lean_uint64_of_nat,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7499624980761693169 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__5_value)
            as *mut crate::leanh::LeanObject,
        4584992172905639687 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__6_value)
            as *mut crate::leanh::LeanObject,
        3878072352281346923 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value:
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
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__8_value)
            as *mut crate::leanh::LeanObject,
        9855511589286918680 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value: crate::leanh::LeanStringObject<60> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 60, m_capacity: 60, m_length: 59, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 101, 108, 97, 98, 95, 114, 117, 108, 101, 115, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 44, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [109, 97, 116, 99, 104, 65, 108, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4_value) as *mut crate::leanh::LeanObject,16529391333736644786 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [124, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__9_value) as *mut crate::leanh::LeanObject,11985596712582660667 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value: crate::leanh::LeanStringObject<62> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 62, m_capacity: 62, m_length: 61, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 101, 108, 97, 98, 95, 114, 117, 108, 101, 115, 32, 97, 108, 116, 101, 114, 110, 97, 116, 105, 118, 101, 44, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__0_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__1_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [44, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__3_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__4_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [101, 108, 97, 98, 82, 117, 108, 101, 115, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__6_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__4_value)
                as *mut crate::leanh::LeanObject,
            8444967374036106427 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__7_value: crate::leanh::LeanStringObject<
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__8_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 46, 84, 101, 114, 109, 69,
        108, 97, 98, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__10_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [84, 101, 114, 109, 69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__11_value: crate::leanh::LeanStringObject<
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
    m_data: [58, 61, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__12_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__12_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__13_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__14_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [115, 116, 120, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__16_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__14_value)
            as *mut crate::leanh::LeanObject,
        5626416068657839193 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__16_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__17_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__17_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__18_value: crate::leanh::LeanStringObject<
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
    m_data: [95, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__18_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__19_value: crate::leanh::LeanStringObject<
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
    m_data: [109, 97, 116, 99, 104, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__19_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__20_value: crate::leanh::LeanStringObject<
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
    m_data: [109, 97, 116, 99, 104, 68, 105, 115, 99, 114, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__20_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__21_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [119, 105, 116, 104, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__22_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__22_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__23_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__23_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__24_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__24_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__25_value: crate::leanh::LeanStringObject<
    23,
> = crate::leanh::LeanStringObject {
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
        116, 104, 114, 111, 119, 85, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 83, 121,
        110, 116, 97, 120, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__27_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__25_value)
            as *mut crate::leanh::LeanObject,
        13300141306757184481 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__27_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__28_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__28: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__28_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__29_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__29: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__30_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__30: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__30_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__28_value)
            as *mut crate::leanh::LeanObject,
        11510100434945111860 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
            as *mut crate::leanh::LeanObject,
        16981400742628996529 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__31_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__31_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__30_value)
            as *mut crate::leanh::LeanObject,
        6797826372810318163 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__31: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__31_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__32_value: crate::leanh::LeanArrayObject<
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__32: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__32_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__33_value: crate::leanh::LeanStringObject<
    30,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 67, 111, 109, 109, 97, 110, 100, 46, 67, 111,
        109, 109, 97, 110, 100, 69, 108, 97, 98, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__33: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__33_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__34_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__34: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__35_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [67, 111, 109, 109, 97, 110, 100, 69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__35: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__35_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__36_value: crate::leanh::LeanStringObject<
    20,
> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 68, 111, 46, 68, 111, 69, 108, 97, 98, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__36: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__36_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__37_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__37: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__38_value: crate::leanh::LeanStringObject<
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
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__38: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__38_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__39_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [68, 111, 69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__39: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__39_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__40_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 111, 110, 116, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__40: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__40_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__41_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__41: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__42_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__40_value)
            as *mut crate::leanh::LeanObject,
        12594597483208894261 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__42: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__42_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__43_value: crate::leanh::LeanStringObject<
    24,
> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 84, 97, 99, 116,
        105, 99, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__43: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__43_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__44_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__44: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__45_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__45: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__45_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__46_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        101, 120, 112, 101, 99, 116, 101, 100, 84, 121, 112, 101, 63, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__46: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__46_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__47_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__47: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__48_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__46_value)
            as *mut crate::leanh::LeanObject,
        15485966262270117935 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__48: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__48_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__49_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__49: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__49_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__50_value: crate::leanh::LeanStringObject<
    32,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 46, 119, 105, 116, 104, 69,
        120, 112, 101, 99, 116, 101, 100, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__50: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__50_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__51_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__51: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__52_value: crate::leanh::LeanStringObject<
    17,
> = crate::leanh::LeanStringObject {
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
        119, 105, 116, 104, 69, 120, 112, 101, 99, 116, 101, 100, 84, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__52: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__52_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__53_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__53: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__53_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__54_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__53_value)
            as *mut crate::leanh::LeanObject,
        8609355255726335675 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__54: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__54_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__55_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 111, 69, 108, 101, 109, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__55: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__55_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__56_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__55_value)
            as *mut crate::leanh::LeanObject,
        12555021329866664416 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__56: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__56_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__57_value: crate::leanh::LeanStringObject<
    18,
> = crate::leanh::LeanStringObject {
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
        115, 121, 110, 116, 97, 120, 32, 99, 97, 116, 101, 103, 111, 114, 121, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__57: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__57_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__58_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__58: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__59_value: crate::leanh::LeanStringObject<
    47,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 47,
    m_capacity: 47,
    m_length: 46,
    m_data: [
        96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 115, 117, 112, 112, 111, 114, 116, 32,
        101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 115, 112, 101, 99, 105,
        102, 105, 99, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__59: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__59_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__60_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__60: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__61_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [100, 111, 69, 108, 101, 109, 95, 101, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__61: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__61_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__62_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__61_value)
            as *mut crate::leanh::LeanObject,
        9031174094084879315 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__62: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__62_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__63_value: crate::leanh::LeanStringObject<
    10,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [116, 101, 114, 109, 95, 101, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__63: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__63_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__64_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__63_value)
            as *mut crate::leanh::LeanObject,
        16126922322386553314 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__64: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__64_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__65_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [99, 111, 109, 109, 97, 110, 100, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__65: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__65_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__66_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__65_value)
            as *mut crate::leanh::LeanObject,
        5063646790596052253 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__66: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__66_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__67_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [116, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__67: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__67_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__68_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__67_value)
            as *mut crate::leanh::LeanObject,
        16145843736367156323 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__68: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__68_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__69_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 111, 110, 118, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__69: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__69_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__70_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__69_value)
            as *mut crate::leanh::LeanObject,
        5852136541633594344 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__70: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__70_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__71_value: crate::leanh::LeanStringObject<
    30,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        117, 110, 115, 117, 112, 112, 111, 114, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32,
        99, 97, 116, 101, 103, 111, 114, 121, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__71: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__71_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__72_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__72: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__73_value: crate::leanh::LeanStringObject<
    13,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [99, 111, 109, 109, 97, 110, 100, 95, 101, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__73: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__73_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__74_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__73_value)
            as *mut crate::leanh::LeanObject,
        2389984077603588103 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__74: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__74_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRulesAux___closed__75_value: crate::leanh::LeanStringObject<
    76,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 76,
    m_capacity: 76,
    m_length: 75,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 101, 108, 97, 98, 95, 114, 117, 108, 101, 115, 32,
        99, 111, 109, 109, 97, 110, 100, 44, 32, 115, 112, 101, 99, 105, 102, 121, 32, 99, 97, 116,
        101, 103, 111, 114, 121, 32, 117, 115, 105, 110, 103, 32, 96, 101, 108, 97, 98, 95, 114,
        117, 108, 101, 115, 32, 58, 32, 60, 99, 97, 116, 62, 32, 46, 46, 46, 96, 0,
    ],
};
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__75: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__75_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__76_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabElabRulesAux___closed__76: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value:
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
    m_data: [60, 61, 0],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value:
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
static mut l_Lean_Elab_Command_elabElabRules___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value:
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
static mut l_Lean_Elab_Command_elabElabRules___lam__1___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__1___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value:
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
static mut l_Lean_Elab_Command_elabElabRules___lam__1___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__1___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value:
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
    m_data: [101, 108, 97, 98, 95, 114, 117, 108, 101, 115, 0],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__0_value)
            as *mut crate::leanh::LeanObject,
        17831573365196998204 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__22_value)
            as *mut crate::leanh::LeanObject,
        13242179749370575553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value:
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
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__3_value)
            as *mut crate::leanh::LeanObject,
        7983999284776576032 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2_value)
            as *mut crate::leanh::LeanObject,
        16572064140653406795 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2533412339571800130 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value:
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
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
            as *mut crate::leanh::LeanObject,
        17342580262104060118 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__6_value)
            as *mut crate::leanh::LeanObject,
        9063780239635860524 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabElabRules___lam__2___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___lam__2___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Command_elabElabRules___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_Command_elabElabRules___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElabRules___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_Command_elabElabRules___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElabRules___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRules___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [101, 108, 97, 98, 69, 108, 97, 98, 82, 117, 108, 101, 115, 0]};
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__28_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__0_value) as *mut crate::leanh::LeanObject,16995956960932422083 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 74 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 81 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 37 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 32 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 74 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 41 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 74 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 41 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 54 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1: usize = 0;
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__3_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__10_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__0_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_elabElab___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__1_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Lean_Elab_Command_elabElab___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [101, 108, 97, 98, 0],
    };
static mut l_Lean_Elab_Command_elabElab___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElab___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabElab___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__3_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__2_value)
                as *mut crate::leanh::LeanObject,
            8571779717108969888 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElab___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__4_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Lean_Elab_Command_elabElab___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElab___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__5_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__5_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabElab___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__5_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__4_value)
                as *mut crate::leanh::LeanObject,
            13348752267415789739 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElab___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__6_value: crate::leanh::LeanStringObject<9> =
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
static mut l_Lean_Elab_Command_elabElab___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__7_value: crate::leanh::LeanStringObject<10> =
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
static mut l_Lean_Elab_Command_elabElab___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__7_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElab___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__8_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__8_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabElab___closed__8_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__8_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__7_value)
                as *mut crate::leanh::LeanObject,
            17682753938374962505 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElab___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__9_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_Command_elabElab___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__10_value: crate::leanh::LeanStringObject<11> =
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
static mut l_Lean_Elab_Command_elabElab___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__10_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElab___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__11_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__11_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabElab___closed__11_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__11_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__10_value)
                as *mut crate::leanh::LeanObject,
            11586196343691998021 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElab___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__12_value: crate::leanh::LeanStringObject<7> =
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
static mut l_Lean_Elab_Command_elabElab___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__12_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElab___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__13_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__13_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__13_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabElab___closed__13_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__13_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__12_value)
                as *mut crate::leanh::LeanObject,
            2812521669163367463 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElab___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__13_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabElab___closed__14_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [101, 108, 97, 98, 84, 97, 105, 108, 0],
    };
static mut l_Lean_Elab_Command_elabElab___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__14_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabElab___closed__15_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__15_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__15_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabElab___closed__15_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__15_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value)
                as *mut crate::leanh::LeanObject,
            17342580262104060118 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabElab___closed__15_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__15_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__14_value)
                as *mut crate::leanh::LeanObject,
            2689576025962180739 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabElab___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabElab___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 97, 98, 69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__28_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_Command_elabElabRulesAux___closed__29_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__0_value) as *mut crate::leanh::LeanObject,714359494884715328 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 84 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 100 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 31 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 84 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 84 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 4 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 12 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(
    mut v_val_3695_: *mut crate::leanh::LeanObject,
    mut v_canonical_3696_: u8,
    mut v___y_3697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3708_: u8 = 0;
    let mut v_a_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3712_: u8 = 0;
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3699_ = l_Lean_Elab_Command_getRef___redArg(v___y_3697_);
                if crate::leanh::lean_obj_tag(v___x_3699_) == 0 {
                    v_a_3700_ = crate::leanh::lean_ctor_get(v___x_3699_, 0);
                    v_isSharedCheck_3708_ = (!crate::leanh::lean_is_exclusive(v___x_3699_)) as u8;
                    if v_isSharedCheck_3708_ == 0 {
                        v___x_3702_ = v___x_3699_;
                        v_isShared_3703_ = v_isSharedCheck_3708_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3700_);
                        crate::leanh::lean_dec(v___x_3699_);
                        v___x_3702_ = crate::leanh::lean_box(0);
                        v_isShared_3703_ = v_isSharedCheck_3708_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_3695_);
                    v_a_3709_ = crate::leanh::lean_ctor_get(v___x_3699_, 0);
                    v_isSharedCheck_3716_ = (!crate::leanh::lean_is_exclusive(v___x_3699_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v___x_3711_ = v___x_3699_;
                        v_isShared_3712_ = v_isSharedCheck_3716_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3709_);
                        crate::leanh::lean_dec(v___x_3699_);
                        v___x_3711_ = crate::leanh::lean_box(0);
                        v_isShared_3712_ = v_isSharedCheck_3716_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3704_ = l_Lean_mkIdentFrom(v_a_3700_, v_val_3695_, v_canonical_3696_);
                crate::leanh::lean_dec(v_a_3700_);
                if v_isShared_3703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3702_, 0, v___x_3704_);
                    v___x_3706_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3704_);
                    v___x_3706_ = v_reuseFailAlloc_3707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3706_;
            }
            3 => {
                if v_isShared_3712_ == 0 {
                    v___x_3714_ = v___x_3711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_a_3709_);
                    v___x_3714_ = v_reuseFailAlloc_3715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3714_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg___boxed(
    mut v_val_3717_: *mut crate::leanh::LeanObject,
    mut v_canonical_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
    mut v___y_3720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonical_boxed_3721_: u8 = 0;
    let mut v_res_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_3721_ = (crate::leanh::lean_unbox(v_canonical_3718_) as u8);
    v_res_3722_ =
        l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(
            v_val_3717_,
            v_canonical_boxed_3721_,
            v___y_3719_,
        );
    crate::leanh::lean_dec_ref(v___y_3719_);
    return v_res_3722_;
}
pub unsafe fn l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(
    mut v_val_3723_: *mut crate::leanh::LeanObject,
    mut v_canonical_3724_: u8,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3728_ =
        l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(
            v_val_3723_,
            v_canonical_3724_,
            v___y_3725_,
        );
    return v___x_3728_;
}
pub unsafe fn l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___boxed(
    mut v_val_3729_: *mut crate::leanh::LeanObject,
    mut v_canonical_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
    mut v___y_3732_: *mut crate::leanh::LeanObject,
    mut v___y_3733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonical_boxed_3734_: u8 = 0;
    let mut v_res_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonical_boxed_3734_ = (crate::leanh::lean_unbox(v_canonical_3730_) as u8);
    v_res_3735_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0(
        v_val_3729_,
        v_canonical_boxed_3734_,
        v___y_3731_,
        v___y_3732_,
    );
    crate::leanh::lean_dec(v___y_3732_);
    crate::leanh::lean_dec_ref(v___y_3731_);
    return v_res_3735_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(
    mut v___y_3736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mainModule_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3738_ = lean_st_ref_get(v___y_3736_);
    v_env_3739_ = crate::leanh::lean_ctor_get(v___x_3738_, 0);
    crate::leanh::lean_inc_ref(v_env_3739_);
    crate::leanh::lean_dec(v___x_3738_);
    v___x_3740_ = l_Lean_Environment_header(v_env_3739_);
    crate::leanh::lean_dec_ref(v_env_3739_);
    v_mainModule_3741_ = crate::leanh::lean_ctor_get(v___x_3740_, 0);
    crate::leanh::lean_inc(v_mainModule_3741_);
    crate::leanh::lean_dec_ref(v___x_3740_);
    v___x_3742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3742_, 0, v_mainModule_3741_);
    return v___x_3742_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg___boxed(
    mut v___y_3743_: *mut crate::leanh::LeanObject,
    mut v___y_3744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3745_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(
        v___y_3743_,
    );
    crate::leanh::lean_dec(v___y_3743_);
    return v_res_3745_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(
    mut v___y_3746_: *mut crate::leanh::LeanObject,
    mut v___y_3747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3749_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(
        v___y_3747_,
    );
    return v___x_3749_;
}
pub unsafe fn l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___boxed(
    mut v___y_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3753_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1(
        v___y_3750_,
        v___y_3751_,
    );
    crate::leanh::lean_dec(v___y_3751_);
    crate::leanh::lean_dec_ref(v___y_3750_);
    return v_res_3753_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3754_ = crate::leanh::lean_box(0);
    v___x_3755_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3756_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3756_, 0, v___x_3755_);
    crate::leanh::lean_ctor_set(v___x_3756_, 1, v___x_3754_);
    return v___x_3756_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3758_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___closed__0);
    v___x_3759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3759_, 0, v___x_3758_);
    return v___x_3759_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg___boxed(
    mut v___y_3760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3761_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
    return v_res_3761_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(
    mut v_00_u03b1_3762_: *mut crate::leanh::LeanObject,
    mut v___y_3763_: *mut crate::leanh::LeanObject,
    mut v___y_3764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3766_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
    return v___x_3766_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___boxed(
    mut v_00_u03b1_3767_: *mut crate::leanh::LeanObject,
    mut v___y_3768_: *mut crate::leanh::LeanObject,
    mut v___y_3769_: *mut crate::leanh::LeanObject,
    mut v___y_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2(
            v_00_u03b1_3767_,
            v___y_3768_,
            v___y_3769_,
        );
    crate::leanh::lean_dec(v___y_3769_);
    crate::leanh::lean_dec_ref(v___y_3768_);
    return v_res_3771_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRulesAux___lam__0(
    mut v_k_3791_: *mut crate::leanh::LeanObject,
    mut v_attrKind_3792_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_3793_: *mut crate::leanh::LeanObject,
    mut v_kind_3794_: *mut crate::leanh::LeanObject,
    mut v___y_3795_: *mut crate::leanh::LeanObject,
    mut v___y_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v_quotContext_x3f_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3830_: u8 = 0;
    let mut v_unused_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v_a_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3843_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3847_: u8 = 0;
    let mut v_a_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3851_: u8 = 0;
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3798_ = 0;
                v___x_3799_ = l_Lean_mkIdentFromRef___at___00Lean_Elab_Command_elabElabRulesAux_spec__0___redArg(v_k_3791_, v___x_3798_, v___y_3795_);
                if crate::leanh::lean_obj_tag(v___x_3799_) == 0 {
                    v_a_3800_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                    crate::leanh::lean_inc(v_a_3800_);
                    crate::leanh::lean_dec_ref_known(v___x_3799_, 1);
                    v___x_3801_ = l_Lean_Elab_Command_getRef___redArg(v___y_3795_);
                    if crate::leanh::lean_obj_tag(v___x_3801_) == 0 {
                        v_a_3802_ = crate::leanh::lean_ctor_get(v___x_3801_, 0);
                        crate::leanh::lean_inc(v_a_3802_);
                        crate::leanh::lean_dec_ref_known(v___x_3801_, 1);
                        v___x_3803_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_3795_);
                        if crate::leanh::lean_obj_tag(v___x_3803_) == 0 {
                            v_isSharedCheck_3830_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3803_)) as u8;
                            if v_isSharedCheck_3830_ == 0 {
                                v_unused_3831_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                                crate::leanh::lean_dec(v_unused_3831_);
                                v___x_3805_ = v___x_3803_;
                                v_isShared_3806_ = v_isSharedCheck_3830_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3803_);
                                v___x_3805_ = crate::leanh::lean_box(0);
                                v_isShared_3806_ = v_isSharedCheck_3830_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3802_);
                            crate::leanh::lean_dec(v_a_3800_);
                            crate::leanh::lean_dec(v_kind_3794_);
                            crate::leanh::lean_dec(v_attrKind_3792_);
                            v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                            v_isSharedCheck_3839_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3803_)) as u8;
                            if v_isSharedCheck_3839_ == 0 {
                                v___x_3834_ = v___x_3803_;
                                v_isShared_3835_ = v_isSharedCheck_3839_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3832_);
                                crate::leanh::lean_dec(v___x_3803_);
                                v___x_3834_ = crate::leanh::lean_box(0);
                                v_isShared_3835_ = v_isSharedCheck_3839_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3800_);
                        crate::leanh::lean_dec(v_kind_3794_);
                        crate::leanh::lean_dec(v_attrKind_3792_);
                        v_a_3840_ = crate::leanh::lean_ctor_get(v___x_3801_, 0);
                        v_isSharedCheck_3847_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3801_)) as u8;
                        if v_isSharedCheck_3847_ == 0 {
                            v___x_3842_ = v___x_3801_;
                            v_isShared_3843_ = v_isSharedCheck_3847_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3840_);
                            crate::leanh::lean_dec(v___x_3801_);
                            v___x_3842_ = crate::leanh::lean_box(0);
                            v_isShared_3843_ = v_isSharedCheck_3847_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_kind_3794_);
                    crate::leanh::lean_dec(v_attrKind_3792_);
                    v_a_3848_ = crate::leanh::lean_ctor_get(v___x_3799_, 0);
                    v_isSharedCheck_3855_ = (!crate::leanh::lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3855_ == 0 {
                        v___x_3850_ = v___x_3799_;
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3848_);
                        crate::leanh::lean_dec(v___x_3799_);
                        v___x_3850_ = crate::leanh::lean_box(0);
                        v_isShared_3851_ = v_isSharedCheck_3855_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_x3f_3807_ = crate::leanh::lean_ctor_get(v___y_3795_, 5);
                v___x_3808_ = l_Lean_SourceInfo_fromRef(v_a_3802_, v___x_3798_);
                crate::leanh::lean_dec(v_a_3802_);
                if crate::leanh::lean_obj_tag(v_quotContext_x3f_3807_) == 0 {
                    v___x_3829_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_3796_);
                    crate::leanh::lean_dec_ref(v___x_3829_);
                    state = 2;
                    continue;
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3810_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__4;
                v___x_3811_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__7;
                v___x_3812_ = lean_mk_syntax_ident(v_kind_3794_);
                v___x_3813_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                crate::leanh::lean_inc_n(v___x_3808_, 2);
                v___x_3814_ = l_Lean_Syntax_node1(v___x_3808_, v___x_3813_, v_a_3800_);
                v___x_3815_ =
                    l_Lean_Syntax_node2(v___x_3808_, v___x_3811_, v___x_3812_, v___x_3814_);
                v___x_3816_ =
                    l_Lean_Syntax_node2(v___x_3808_, v___x_3810_, v_attrKind_3792_, v___x_3815_);
                if crate::leanh::lean_obj_tag(v_attrs_x3f_3793_) == 0 {
                    v___x_3817_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3818_ = lean_mk_empty_array_with_capacity(v___x_3817_);
                    v___x_3819_ = lean_array_push(v___x_3818_, v___x_3816_);
                    if v_isShared_3806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3819_);
                        v___x_3821_ = v___x_3805_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
                        v___x_3821_ = v_reuseFailAlloc_3822_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_val_3823_ = crate::leanh::lean_ctor_get(v_attrs_x3f_3793_, 0);
                    v___x_3824_ = l_Lean_Syntax_TSepArray_getElems___redArg(v_val_3823_);
                    v___x_3825_ = lean_array_push(v___x_3824_, v___x_3816_);
                    if v_isShared_3806_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3805_, 0, v___x_3825_);
                        v___x_3827_ = v___x_3805_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3828_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
                        v___x_3827_ = v_reuseFailAlloc_3828_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_3821_;
            }
            4 => {
                return v___x_3827_;
            }
            5 => {
                if v_isShared_3835_ == 0 {
                    v___x_3837_ = v___x_3834_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3837_;
            }
            7 => {
                if v_isShared_3843_ == 0 {
                    v___x_3845_ = v___x_3842_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
                    v___x_3845_ = v_reuseFailAlloc_3846_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3845_;
            }
            9 => {
                if v_isShared_3851_ == 0 {
                    v___x_3853_ = v___x_3850_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3854_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
                    v___x_3853_ = v_reuseFailAlloc_3854_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabElabRulesAux___lam__0___boxed(
    mut v_k_3856_: *mut crate::leanh::LeanObject,
    mut v_attrKind_3857_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_3858_: *mut crate::leanh::LeanObject,
    mut v_kind_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3863_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
        v_k_3856_,
        v_attrKind_3857_,
        v_attrs_x3f_3858_,
        v_kind_3859_,
        v___y_3860_,
        v___y_3861_,
    );
    crate::leanh::lean_dec(v___y_3861_);
    crate::leanh::lean_dec_ref(v___y_3860_);
    crate::leanh::lean_dec(v_attrs_x3f_3858_);
    return v_res_3863_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(
    mut v_opts_3864_: *mut crate::leanh::LeanObject,
    mut v_opt_3865_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3866_ = crate::leanh::lean_ctor_get(v_opt_3865_, 0);
    v_defValue_3867_ = crate::leanh::lean_ctor_get(v_opt_3865_, 1);
    v_map_3868_ = crate::leanh::lean_ctor_get(v_opts_3864_, 0);
    v___x_3869_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3868_,
            v_name_3866_,
        );
    if crate::leanh::lean_obj_tag(v___x_3869_) == 0 {
        let mut v___x_3870_: u8 = 0;
        v___x_3870_ = (crate::leanh::lean_unbox(v_defValue_3867_) as u8);
        return v___x_3870_;
    } else {
        let mut v_val_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3871_ = crate::leanh::lean_ctor_get(v___x_3869_, 0);
        crate::leanh::lean_inc(v_val_3871_);
        crate::leanh::lean_dec_ref_known(v___x_3869_, 1);
        if crate::leanh::lean_obj_tag(v_val_3871_) == 1 {
            let mut v_v_3872_: u8 = 0;
            v_v_3872_ = crate::leanh::lean_ctor_get_uint8(v_val_3871_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3871_, 0);
            return v_v_3872_;
        } else {
            let mut v___x_3873_: u8 = 0;
            crate::leanh::lean_dec(v_val_3871_);
            v___x_3873_ = (crate::leanh::lean_unbox(v_defValue_3867_) as u8);
            return v___x_3873_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8___boxed(
    mut v_opts_3874_: *mut crate::leanh::LeanObject,
    mut v_opt_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3876_: u8 = 0;
    let mut v_r_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3876_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_3874_, v_opt_3875_);
    crate::leanh::lean_dec_ref(v_opt_3875_);
    crate::leanh::lean_dec_ref(v_opts_3874_);
    v_r_3877_ = crate::leanh::lean_box((v_res_3876_) as usize);
    return v_r_3877_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3878_ = crate::leanh::lean_box(1);
    v___x_3879_ = l_Lean_MessageData_ofFormat(v___x_3878_);
    return v___x_3879_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3883_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__2;
    v___x_3884_ = l_Lean_MessageData_ofFormat(v___x_3883_);
    return v___x_3884_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(
    mut v_x_3885_: *mut crate::leanh::LeanObject,
    mut v_x_3886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3891_: u8 = 0;
    let mut v_before_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3908_: u8 = 0;
    let mut v_unused_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3886_) == 0 {
                    return v_x_3885_;
                } else {
                    v_head_3887_ = crate::leanh::lean_ctor_get(v_x_3886_, 0);
                    v_tail_3888_ = crate::leanh::lean_ctor_get(v_x_3886_, 1);
                    v_isSharedCheck_3910_ = (!crate::leanh::lean_is_exclusive(v_x_3886_)) as u8;
                    if v_isSharedCheck_3910_ == 0 {
                        v___x_3890_ = v_x_3886_;
                        v_isShared_3891_ = v_isSharedCheck_3910_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3888_);
                        crate::leanh::lean_inc(v_head_3887_);
                        crate::leanh::lean_dec(v_x_3886_);
                        v___x_3890_ = crate::leanh::lean_box(0);
                        v_isShared_3891_ = v_isSharedCheck_3910_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_3892_ = crate::leanh::lean_ctor_get(v_head_3887_, 0);
                v_isSharedCheck_3908_ = (!crate::leanh::lean_is_exclusive(v_head_3887_)) as u8;
                if v_isSharedCheck_3908_ == 0 {
                    v_unused_3909_ = crate::leanh::lean_ctor_get(v_head_3887_, 1);
                    crate::leanh::lean_dec(v_unused_3909_);
                    v___x_3894_ = v_head_3887_;
                    v_isShared_3895_ = v_isSharedCheck_3908_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_3892_);
                    crate::leanh::lean_dec(v_head_3887_);
                    v___x_3894_ = crate::leanh::lean_box(0);
                    v_isShared_3895_ = v_isSharedCheck_3908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3896_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_3895_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3894_, 7);
                    crate::leanh::lean_ctor_set(v___x_3894_, 1, v___x_3896_);
                    crate::leanh::lean_ctor_set(v___x_3894_, 0, v_x_3885_);
                    v___x_3898_ = v___x_3894_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3907_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_x_3885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3896_);
                    v___x_3898_ = v_reuseFailAlloc_3907_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3899_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__3);
                if v_isShared_3891_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3890_, 7);
                    crate::leanh::lean_ctor_set(v___x_3890_, 1, v___x_3899_);
                    crate::leanh::lean_ctor_set(v___x_3890_, 0, v___x_3898_);
                    v___x_3901_ = v___x_3890_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3906_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3906_, 1, v___x_3899_);
                    v___x_3901_ = v_reuseFailAlloc_3906_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3902_ = l_Lean_MessageData_ofSyntax(v_before_3892_);
                v___x_3903_ = l_Lean_indentD(v___x_3902_);
                v___x_3904_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3904_, 0, v___x_3901_);
                crate::leanh::lean_ctor_set(v___x_3904_, 1, v___x_3903_);
                v_x_3885_ = v___x_3904_;
                v_x_3886_ = v_tail_3888_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3914_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__1;
    v___x_3915_ = l_Lean_MessageData_ofFormat(v___x_3914_);
    return v___x_3915_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(
    mut v_msgData_3916_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3933_: u8 = 0;
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut v_unused_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3920_ = lean_st_ref_get(v___y_3918_);
                v_scopes_3921_ = crate::leanh::lean_ctor_get(v___x_3920_, 2);
                crate::leanh::lean_inc(v_scopes_3921_);
                crate::leanh::lean_dec(v___x_3920_);
                v___x_3922_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_3923_ = l_List_head_x21___redArg(v___x_3922_, v_scopes_3921_);
                crate::leanh::lean_dec(v_scopes_3921_);
                v_opts_3924_ = crate::leanh::lean_ctor_get(v___x_3923_, 1);
                crate::leanh::lean_inc_ref(v_opts_3924_);
                crate::leanh::lean_dec(v___x_3923_);
                v___x_3925_ = l_Lean_Elab_pp_macroStack;
                v___x_3926_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__8(v_opts_3924_, v___x_3925_);
                crate::leanh::lean_dec_ref(v_opts_3924_);
                if v___x_3926_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_3917_);
                    v___x_3927_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3927_, 0, v_msgData_3916_);
                    return v___x_3927_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_3917_) == 0 {
                        v___x_3928_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3928_, 0, v_msgData_3916_);
                        return v___x_3928_;
                    } else {
                        v_head_3929_ = crate::leanh::lean_ctor_get(v_macroStack_3917_, 0);
                        crate::leanh::lean_inc(v_head_3929_);
                        v_after_3930_ = crate::leanh::lean_ctor_get(v_head_3929_, 1);
                        v_isSharedCheck_3945_ =
                            (!crate::leanh::lean_is_exclusive(v_head_3929_)) as u8;
                        if v_isSharedCheck_3945_ == 0 {
                            v_unused_3946_ = crate::leanh::lean_ctor_get(v_head_3929_, 0);
                            crate::leanh::lean_dec(v_unused_3946_);
                            v___x_3932_ = v_head_3929_;
                            v_isShared_3933_ = v_isSharedCheck_3945_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_3930_);
                            crate::leanh::lean_dec(v_head_3929_);
                            v___x_3932_ = crate::leanh::lean_box(0);
                            v_isShared_3933_ = v_isSharedCheck_3945_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3934_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9___closed__0);
                if v_isShared_3933_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3932_, 7);
                    crate::leanh::lean_ctor_set(v___x_3932_, 1, v___x_3934_);
                    crate::leanh::lean_ctor_set(v___x_3932_, 0, v_msgData_3916_);
                    v___x_3936_ = v___x_3932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3944_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_msgData_3916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 1, v___x_3934_);
                    v___x_3936_ = v_reuseFailAlloc_3944_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3937_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___closed__2);
                v___x_3938_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3938_, 0, v___x_3936_);
                crate::leanh::lean_ctor_set(v___x_3938_, 1, v___x_3937_);
                v___x_3939_ = l_Lean_MessageData_ofSyntax(v_after_3930_);
                v___x_3940_ = l_Lean_indentD(v___x_3939_);
                v_msgData_3941_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_3941_, 0, v___x_3938_);
                crate::leanh::lean_ctor_set(v_msgData_3941_, 1, v___x_3940_);
                v___x_3942_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7_spec__9(v_msgData_3941_, v_macroStack_3917_);
                v___x_3943_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3943_, 0, v___x_3942_);
                return v___x_3943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg___boxed(
    mut v_msgData_3947_: *mut crate::leanh::LeanObject,
    mut v_macroStack_3948_: *mut crate::leanh::LeanObject,
    mut v___y_3949_: *mut crate::leanh::LeanObject,
    mut v___y_3950_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3951_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_3947_, v_macroStack_3948_, v___y_3949_);
    crate::leanh::lean_dec(v___y_3949_);
    return v_res_3951_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3952_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3952_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3953_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__0);
    v___x_3954_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3954_, 0, v___x_3953_);
    return v___x_3954_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3955_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
    v___x_3956_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3957_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3957_, 0, v___x_3956_);
    crate::leanh::lean_ctor_set(v___x_3957_, 1, v___x_3956_);
    crate::leanh::lean_ctor_set(v___x_3957_, 2, v___x_3956_);
    crate::leanh::lean_ctor_set(v___x_3957_, 3, v___x_3956_);
    crate::leanh::lean_ctor_set(v___x_3957_, 4, v___x_3955_);
    crate::leanh::lean_ctor_set(v___x_3957_, 5, v___x_3955_);
    crate::leanh::lean_ctor_set(v___x_3957_, 6, v___x_3955_);
    crate::leanh::lean_ctor_set(v___x_3957_, 7, v___x_3955_);
    crate::leanh::lean_ctor_set(v___x_3957_, 8, v___x_3955_);
    crate::leanh::lean_ctor_set(v___x_3957_, 9, v___x_3955_);
    return v___x_3957_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3959_ = lean_mk_empty_array_with_capacity(v___x_3958_);
    v___x_3960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3960_, 0, v___x_3959_);
    return v___x_3960_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: usize = 0;
    let mut v___x_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3961_ = 5usize;
    v___x_3962_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3963_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_3964_ = lean_mk_empty_array_with_capacity(v___x_3963_);
    v___x_3965_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__3);
    v___x_3966_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_3966_, 0, v___x_3965_);
    crate::leanh::lean_ctor_set(v___x_3966_, 1, v___x_3964_);
    crate::leanh::lean_ctor_set(v___x_3966_, 2, v___x_3962_);
    crate::leanh::lean_ctor_set(v___x_3966_, 3, v___x_3962_);
    crate::leanh::lean_ctor_set_usize(v___x_3966_, 4, v___x_3961_);
    return v___x_3966_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3967_ = crate::leanh::lean_box(1);
    v___x_3968_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__4);
    v___x_3969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__1);
    v___x_3970_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3970_, 0, v___x_3969_);
    crate::leanh::lean_ctor_set(v___x_3970_, 1, v___x_3968_);
    crate::leanh::lean_ctor_set(v___x_3970_, 2, v___x_3967_);
    return v___x_3970_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(
    mut v_msgData_3971_: *mut crate::leanh::LeanObject,
    mut v___y_3972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3974_ = lean_st_ref_get(v___y_3972_);
    v_env_3975_ = crate::leanh::lean_ctor_get(v___x_3974_, 0);
    crate::leanh::lean_inc_ref(v_env_3975_);
    crate::leanh::lean_dec(v___x_3974_);
    v___x_3976_ = lean_st_ref_get(v___y_3972_);
    v_scopes_3977_ = crate::leanh::lean_ctor_get(v___x_3976_, 2);
    crate::leanh::lean_inc(v_scopes_3977_);
    crate::leanh::lean_dec(v___x_3976_);
    v___x_3978_ = l_Lean_Elab_Command_instInhabitedScope_default;
    v___x_3979_ = l_List_head_x21___redArg(v___x_3978_, v_scopes_3977_);
    crate::leanh::lean_dec(v_scopes_3977_);
    v_opts_3980_ = crate::leanh::lean_ctor_get(v___x_3979_, 1);
    crate::leanh::lean_inc_ref(v_opts_3980_);
    crate::leanh::lean_dec(v___x_3979_);
    v___x_3981_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__2);
    v___x_3982_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___closed__5);
    v___x_3983_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3983_, 0, v_env_3975_);
    crate::leanh::lean_ctor_set(v___x_3983_, 1, v___x_3981_);
    crate::leanh::lean_ctor_set(v___x_3983_, 2, v___x_3982_);
    crate::leanh::lean_ctor_set(v___x_3983_, 3, v_opts_3980_);
    v___x_3984_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_3983_);
    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_msgData_3971_);
    v___x_3985_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3985_, 0, v___x_3984_);
    return v___x_3985_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg___boxed(
    mut v_msgData_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_3986_, v___y_3987_);
    crate::leanh::lean_dec(v___y_3987_);
    return v_res_3989_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(
    mut v_msg_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4004_: u8 = 0;
    let mut v___x_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4009_: u8 = 0;
    let mut v_a_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4013_: u8 = 0;
    let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3994_ = l_Lean_Elab_Command_getRef___redArg(v___y_3991_);
                if crate::leanh::lean_obj_tag(v___x_3994_) == 0 {
                    v_a_3995_ = crate::leanh::lean_ctor_get(v___x_3994_, 0);
                    crate::leanh::lean_inc(v_a_3995_);
                    crate::leanh::lean_dec_ref_known(v___x_3994_, 1);
                    v_macroStack_3996_ = crate::leanh::lean_ctor_get(v___y_3991_, 4);
                    v___x_3997_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_3990_, v___y_3992_);
                    v_a_3998_ = crate::leanh::lean_ctor_get(v___x_3997_, 0);
                    crate::leanh::lean_inc(v_a_3998_);
                    crate::leanh::lean_dec_ref(v___x_3997_);
                    v___x_3999_ = l_Lean_Elab_getBetterRef(v_a_3995_, v_macroStack_3996_);
                    crate::leanh::lean_dec(v_a_3995_);
                    crate::leanh::lean_inc(v_macroStack_3996_);
                    v___x_4000_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_a_3998_, v_macroStack_3996_, v___y_3992_);
                    v_a_4001_ = crate::leanh::lean_ctor_get(v___x_4000_, 0);
                    v_isSharedCheck_4009_ = (!crate::leanh::lean_is_exclusive(v___x_4000_)) as u8;
                    if v_isSharedCheck_4009_ == 0 {
                        v___x_4003_ = v___x_4000_;
                        v_isShared_4004_ = v_isSharedCheck_4009_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4001_);
                        crate::leanh::lean_dec(v___x_4000_);
                        v___x_4003_ = crate::leanh::lean_box(0);
                        v_isShared_4004_ = v_isSharedCheck_4009_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_3990_);
                    v_a_4010_ = crate::leanh::lean_ctor_get(v___x_3994_, 0);
                    v_isSharedCheck_4017_ = (!crate::leanh::lean_is_exclusive(v___x_3994_)) as u8;
                    if v_isSharedCheck_4017_ == 0 {
                        v___x_4012_ = v___x_3994_;
                        v_isShared_4013_ = v_isSharedCheck_4017_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4010_);
                        crate::leanh::lean_dec(v___x_3994_);
                        v___x_4012_ = crate::leanh::lean_box(0);
                        v_isShared_4013_ = v_isSharedCheck_4017_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4005_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4005_, 0, v___x_3999_);
                crate::leanh::lean_ctor_set(v___x_4005_, 1, v_a_4001_);
                if v_isShared_4004_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4003_, 1);
                    crate::leanh::lean_ctor_set(v___x_4003_, 0, v___x_4005_);
                    v___x_4007_ = v___x_4003_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4008_, 0, v___x_4005_);
                    v___x_4007_ = v_reuseFailAlloc_4008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4007_;
            }
            3 => {
                if v_isShared_4013_ == 0 {
                    v___x_4015_ = v___x_4012_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4016_, 0, v_a_4010_);
                    v___x_4015_ = v_reuseFailAlloc_4016_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg___boxed(
    mut v_msg_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4022_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(
        v_msg_4018_,
        v___y_4019_,
        v___y_4020_,
    );
    crate::leanh::lean_dec(v___y_4020_);
    crate::leanh::lean_dec_ref(v___y_4019_);
    return v_res_4022_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(
    mut v_ref_4023_: *mut crate::leanh::LeanObject,
    mut v_msg_4024_: *mut crate::leanh::LeanObject,
    mut v___y_4025_: *mut crate::leanh::LeanObject,
    mut v___y_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cmdPos_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snap_x3f_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cancelTk_x3f_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4039_: u8 = 0;
    let mut v_ref_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4050_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4028_ = l_Lean_Elab_Command_getRef___redArg(v___y_4025_);
                if crate::leanh::lean_obj_tag(v___x_4028_) == 0 {
                    v_a_4029_ = crate::leanh::lean_ctor_get(v___x_4028_, 0);
                    crate::leanh::lean_inc(v_a_4029_);
                    crate::leanh::lean_dec_ref_known(v___x_4028_, 1);
                    v_fileName_4030_ = crate::leanh::lean_ctor_get(v___y_4025_, 0);
                    v_fileMap_4031_ = crate::leanh::lean_ctor_get(v___y_4025_, 1);
                    v_currRecDepth_4032_ = crate::leanh::lean_ctor_get(v___y_4025_, 2);
                    v_cmdPos_4033_ = crate::leanh::lean_ctor_get(v___y_4025_, 3);
                    v_macroStack_4034_ = crate::leanh::lean_ctor_get(v___y_4025_, 4);
                    v_quotContext_x3f_4035_ = crate::leanh::lean_ctor_get(v___y_4025_, 5);
                    v_currMacroScope_4036_ = crate::leanh::lean_ctor_get(v___y_4025_, 6);
                    v_snap_x3f_4037_ = crate::leanh::lean_ctor_get(v___y_4025_, 8);
                    v_cancelTk_x3f_4038_ = crate::leanh::lean_ctor_get(v___y_4025_, 9);
                    v_suppressElabErrors_4039_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4025_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                    );
                    v_ref_4040_ = l_Lean_replaceRef(v_ref_4023_, v_a_4029_);
                    crate::leanh::lean_dec(v_a_4029_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_4038_);
                    crate::leanh::lean_inc(v_snap_x3f_4037_);
                    crate::leanh::lean_inc(v_currMacroScope_4036_);
                    crate::leanh::lean_inc(v_quotContext_x3f_4035_);
                    crate::leanh::lean_inc(v_macroStack_4034_);
                    crate::leanh::lean_inc(v_cmdPos_4033_);
                    crate::leanh::lean_inc(v_currRecDepth_4032_);
                    crate::leanh::lean_inc_ref(v_fileMap_4031_);
                    crate::leanh::lean_inc_ref(v_fileName_4030_);
                    v___x_4041_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v___x_4041_, 0, v_fileName_4030_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 1, v_fileMap_4031_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 2, v_currRecDepth_4032_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 3, v_cmdPos_4033_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 4, v_macroStack_4034_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 5, v_quotContext_x3f_4035_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 6, v_currMacroScope_4036_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 7, v_ref_4040_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 8, v_snap_x3f_4037_);
                    crate::leanh::lean_ctor_set(v___x_4041_, 9, v_cancelTk_x3f_4038_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4041_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_suppressElabErrors_4039_,
                    );
                    v___x_4042_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v_msg_4024_, v___x_4041_, v___y_4026_);
                    crate::leanh::lean_dec_ref_known(v___x_4041_, 10);
                    return v___x_4042_;
                } else {
                    crate::leanh::lean_dec_ref(v_msg_4024_);
                    v_a_4043_ = crate::leanh::lean_ctor_get(v___x_4028_, 0);
                    v_isSharedCheck_4050_ = (!crate::leanh::lean_is_exclusive(v___x_4028_)) as u8;
                    if v_isSharedCheck_4050_ == 0 {
                        v___x_4045_ = v___x_4028_;
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4043_);
                        crate::leanh::lean_dec(v___x_4028_);
                        v___x_4045_ = crate::leanh::lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4050_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4046_ == 0 {
                    v___x_4048_ = v___x_4045_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4049_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4049_, 0, v_a_4043_);
                    v___x_4048_ = v_reuseFailAlloc_4049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4048_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg___boxed(
    mut v_ref_4051_: *mut crate::leanh::LeanObject,
    mut v_msg_4052_: *mut crate::leanh::LeanObject,
    mut v___y_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4056_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(
        v_ref_4051_,
        v_msg_4052_,
        v___y_4053_,
        v___y_4054_,
    );
    crate::leanh::lean_dec(v___y_4054_);
    crate::leanh::lean_dec_ref(v___y_4053_);
    crate::leanh::lean_dec(v_ref_4051_);
    return v_res_4056_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(
    mut v_k_4060_: *mut crate::leanh::LeanObject,
    mut v_as_4061_: *mut crate::leanh::LeanObject,
    mut v_sz_4062_: usize,
    mut v_i_4063_: usize,
    mut v_b_4064_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4065_: u8 = 0;
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: u8 = 0;
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: usize = 0;
    let mut v___x_4072_: usize = 0;
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4065_ = lean_usize_dec_lt(v_i_4063_, v_sz_4062_);
                if v___x_4065_ == 0 {
                    crate::leanh::lean_dec(v_k_4060_);
                    crate::leanh::lean_inc_ref(v_b_4064_);
                    return v_b_4064_;
                } else {
                    v___x_4066_ = crate::leanh::lean_box(0);
                    v_a_4067_ = lean_array_uget_borrowed(v_as_4061_, v_i_4063_);
                    crate::leanh::lean_inc(v_a_4067_);
                    v___x_4068_ = l_Lean_Syntax_getKind(v_a_4067_);
                    crate::leanh::lean_inc(v_k_4060_);
                    v___x_4069_ = l_Lean_Elab_Command_checkRuleKind(v___x_4068_, v_k_4060_);
                    crate::leanh::lean_dec(v___x_4068_);
                    if v___x_4069_ == 0 {
                        v___x_4070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0;
                        v___x_4071_ = 1usize;
                        v___x_4072_ = lean_usize_add(v_i_4063_, v___x_4071_);
                        v_i_4063_ = v___x_4072_;
                        v_b_4064_ = v___x_4070_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_4060_);
                        crate::leanh::lean_inc(v_a_4067_);
                        v___x_4074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4074_, 0, v_a_4067_);
                        v___x_4075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4074_);
                        v___x_4076_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4076_, 0, v___x_4075_);
                        crate::leanh::lean_ctor_set(v___x_4076_, 1, v___x_4066_);
                        return v___x_4076_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___boxed(
    mut v_k_4077_: *mut crate::leanh::LeanObject,
    mut v_as_4078_: *mut crate::leanh::LeanObject,
    mut v_sz_4079_: *mut crate::leanh::LeanObject,
    mut v_i_4080_: *mut crate::leanh::LeanObject,
    mut v_b_4081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4082_: usize = 0;
    let mut v_i_boxed_4083_: usize = 0;
    let mut v_res_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4082_ = crate::leanh::lean_unbox_usize(v_sz_4079_);
    crate::leanh::lean_dec(v_sz_4079_);
    v_i_boxed_4083_ = crate::leanh::lean_unbox_usize(v_i_4080_);
    crate::leanh::lean_dec(v_i_4080_);
    v_res_4084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_4077_, v_as_4078_, v_sz_boxed_4082_, v_i_boxed_4083_, v_b_4081_);
    crate::leanh::lean_dec_ref(v_b_4081_);
    crate::leanh::lean_dec_ref(v_as_4078_);
    return v_res_4084_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__0;
    v___x_4087_ = l_Lean_stringToMessageData(v___x_4086_);
    return v___x_4087_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4089_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__2;
    v___x_4090_ = l_Lean_stringToMessageData(v___x_4089_);
    return v___x_4090_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4098_ = l_Array_mkArray0(crate::leanh::lean_box(0));
    return v___x_4098_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4104_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__11;
    v___x_4105_ = l_Lean_stringToMessageData(v___x_4104_);
    return v___x_4105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(
    mut v_k_4106_: *mut crate::leanh::LeanObject,
    mut v_sz_4107_: usize,
    mut v_i_4108_: usize,
    mut v_bs_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4113_: u8 = 0;
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: usize = 0;
    let mut v___x_4121_: usize = 0;
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4130_: u8 = 0;
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4134_: u8 = 0;
    let mut v___y_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: u8 = 0;
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pat_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quoted_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: u8 = 0;
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: u8 = 0;
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4186_: usize = 0;
    let mut v___x_4187_: usize = 0;
    let mut v___x_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pat_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4203_: u8 = 0;
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4207_: u8 = 0;
    let mut v_a_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4211_: u8 = 0;
    let mut v___x_4213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4215_: u8 = 0;
    let mut v_a_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4219_: u8 = 0;
    let mut v___x_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4223_: u8 = 0;
    let mut v___x_4224_: u8 = 0;
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4229_: u8 = 0;
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4113_ = lean_usize_dec_lt(v_i_4108_, v_sz_4107_);
                if v___x_4113_ == 0 {
                    crate::leanh::lean_dec(v_k_4106_);
                    v___x_4114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4114_, 0, v_bs_4109_);
                    return v___x_4114_;
                } else {
                    v_v_4115_ = lean_array_uget(v_bs_4109_, v_i_4108_);
                    v___x_4116_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4117_ = lean_array_uset(v_bs_4109_, v_i_4108_, v___x_4116_);
                    v___x_4144_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__5;
                    crate::leanh::lean_inc(v_v_4115_);
                    v___x_4145_ = l_Lean_Syntax_isOfKind(v_v_4115_, v___x_4144_);
                    if v___x_4145_ == 0 {
                        crate::leanh::lean_dec(v_v_4115_);
                        v___x_4146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        v___y_4125_ = v___x_4146_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4147_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4148_ = l_Lean_Syntax_getArg(v_v_4115_, v___x_4147_);
                        crate::leanh::lean_inc(v___x_4148_);
                        v___x_4149_ = l_Lean_Syntax_matchesNull(v___x_4148_, v___x_4147_);
                        if v___x_4149_ == 0 {
                            crate::leanh::lean_dec(v___x_4148_);
                            crate::leanh::lean_dec(v_v_4115_);
                            v___x_4150_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            v___y_4125_ = v___x_4150_;
                            state = 2;
                            continue;
                        } else {
                            v___x_4151_ = l_Lean_Syntax_getArg(v___x_4148_, v___x_4116_);
                            crate::leanh::lean_dec(v___x_4148_);
                            v___x_4152_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_4153_ = l_Lean_Syntax_getArg(v_v_4115_, v___x_4152_);
                            v___x_4167_ = l_Lean_Syntax_getArgs(v___x_4151_);
                            crate::leanh::lean_dec(v___x_4151_);
                            v___x_4168_ = crate::leanh::lean_box(0);
                            v_pat_4169_ = lean_array_get(v___x_4168_, v___x_4167_, v___x_4116_);
                            v___x_4224_ = l_Lean_Syntax_isQuot(v_pat_4169_);
                            if v___x_4224_ == 0 {
                                if v___x_4149_ == 0 {
                                    v___y_4171_ = v___y_4110_;
                                    v___y_4172_ = v___y_4111_;
                                    state = 7;
                                    continue;
                                } else {
                                    v___x_4225_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                                    if crate::leanh::lean_obj_tag(v___x_4225_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4225_, 1);
                                        v___y_4171_ = v___y_4110_;
                                        v___y_4172_ = v___y_4111_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_pat_4169_);
                                        crate::leanh::lean_dec_ref(v___x_4167_);
                                        crate::leanh::lean_dec(v___x_4153_);
                                        crate::leanh::lean_dec_ref(v_bs_x27_4117_);
                                        crate::leanh::lean_dec(v_v_4115_);
                                        crate::leanh::lean_dec(v_k_4106_);
                                        v_a_4226_ = crate::leanh::lean_ctor_get(v___x_4225_, 0);
                                        v_isSharedCheck_4233_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4225_)) as u8;
                                        if v_isSharedCheck_4233_ == 0 {
                                            v___x_4228_ = v___x_4225_;
                                            v_isShared_4229_ = v_isSharedCheck_4233_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4226_);
                                            crate::leanh::lean_dec(v___x_4225_);
                                            v___x_4228_ = crate::leanh::lean_box(0);
                                            v_isShared_4229_ = v_isSharedCheck_4233_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                v___y_4171_ = v___y_4110_;
                                v___y_4172_ = v___y_4111_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4120_ = 1usize;
                v___x_4121_ = lean_usize_add(v_i_4108_, v___x_4120_);
                v___x_4122_ = lean_array_uset(v_bs_x27_4117_, v_i_4108_, v_a_4119_);
                v_i_4108_ = v___x_4121_;
                v_bs_4109_ = v___x_4122_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4125_) == 0 {
                    v_a_4126_ = crate::leanh::lean_ctor_get(v___y_4125_, 0);
                    crate::leanh::lean_inc(v_a_4126_);
                    crate::leanh::lean_dec_ref_known(v___y_4125_, 1);
                    v_a_4119_ = v_a_4126_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_4117_);
                    crate::leanh::lean_dec(v_k_4106_);
                    v_a_4127_ = crate::leanh::lean_ctor_get(v___y_4125_, 0);
                    v_isSharedCheck_4134_ = (!crate::leanh::lean_is_exclusive(v___y_4125_)) as u8;
                    if v_isSharedCheck_4134_ == 0 {
                        v___x_4129_ = v___y_4125_;
                        v_isShared_4130_ = v_isSharedCheck_4134_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4127_);
                        crate::leanh::lean_dec(v___y_4125_);
                        v___x_4129_ = crate::leanh::lean_box(0);
                        v_isShared_4130_ = v_isSharedCheck_4134_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4130_ == 0 {
                    v___x_4132_ = v___x_4129_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
                    v___x_4132_ = v_reuseFailAlloc_4133_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4132_;
            }
            5 => {
                v___x_4138_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__1);
                crate::leanh::lean_inc(v_k_4106_);
                v___x_4139_ = l_Lean_MessageData_ofName(v_k_4106_);
                v___x_4140_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4140_, 0, v___x_4138_);
                crate::leanh::lean_ctor_set(v___x_4140_, 1, v___x_4139_);
                v___x_4141_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
                v___x_4142_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4142_, 0, v___x_4140_);
                crate::leanh::lean_ctor_set(v___x_4142_, 1, v___x_4141_);
                v___x_4143_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_4115_, v___x_4142_, v___y_4136_, v___y_4137_);
                crate::leanh::lean_dec(v_v_4115_);
                v___y_4125_ = v___x_4143_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                crate::leanh::lean_inc_n(v___y_4156_, 4);
                v___x_4158_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4158_, 0, v___y_4156_);
                crate::leanh::lean_ctor_set(v___x_4158_, 1, v___x_4157_);
                v___x_4159_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_4160_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                v___x_4161_ = l_Array_append___redArg(v___x_4160_, v___y_4155_);
                crate::leanh::lean_dec_ref(v___y_4155_);
                v___x_4162_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4162_, 0, v___y_4156_);
                crate::leanh::lean_ctor_set(v___x_4162_, 1, v___x_4159_);
                crate::leanh::lean_ctor_set(v___x_4162_, 2, v___x_4161_);
                v___x_4163_ = l_Lean_Syntax_node1(v___y_4156_, v___x_4159_, v___x_4162_);
                v___x_4164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_4165_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4165_, 0, v___y_4156_);
                crate::leanh::lean_ctor_set(v___x_4165_, 1, v___x_4164_);
                v___x_4166_ = l_Lean_Syntax_node4(
                    v___y_4156_,
                    v___x_4144_,
                    v___x_4158_,
                    v___x_4163_,
                    v___x_4165_,
                    v___x_4153_,
                );
                v_a_4119_ = v___x_4166_;
                state = 1;
                continue;
            }
            7 => {
                crate::leanh::lean_inc(v_pat_4169_);
                v_quoted_4173_ = l_Lean_Syntax_getQuotContent(v_pat_4169_);
                crate::leanh::lean_inc(v_quoted_4173_);
                v_k_x27_4174_ = l_Lean_Syntax_getKind(v_quoted_4173_);
                crate::leanh::lean_inc(v_k_4106_);
                v___x_4175_ = l_Lean_Elab_Command_checkRuleKind(v_k_x27_4174_, v_k_4106_);
                if v___x_4175_ == 0 {
                    v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__10;
                    v___x_4177_ = lean_name_eq(v_k_x27_4174_, v___x_4176_);
                    if v___x_4177_ == 0 {
                        crate::leanh::lean_dec(v_quoted_4173_);
                        crate::leanh::lean_dec(v_pat_4169_);
                        crate::leanh::lean_dec_ref(v___x_4167_);
                        crate::leanh::lean_dec(v___x_4153_);
                        v___x_4178_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__12);
                        v___x_4179_ = l_Lean_MessageData_ofName(v_k_x27_4174_);
                        v___x_4180_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4180_, 0, v___x_4178_);
                        crate::leanh::lean_ctor_set(v___x_4180_, 1, v___x_4179_);
                        v___x_4181_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
                        v___x_4182_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4182_, 0, v___x_4180_);
                        crate::leanh::lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                        v___x_4183_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_v_4115_, v___x_4182_, v___y_4171_, v___y_4172_);
                        crate::leanh::lean_dec(v_v_4115_);
                        v___y_4125_ = v___x_4183_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_k_x27_4174_);
                        v___x_4184_ = l_Lean_Syntax_getArgs(v_quoted_4173_);
                        crate::leanh::lean_dec(v_quoted_4173_);
                        v___x_4185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4___closed__0;
                        v_sz_4186_ = lean_array_size(v___x_4184_);
                        v___x_4187_ = 0usize;
                        crate::leanh::lean_inc(v_k_4106_);
                        v___x_4188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Command_elabElabRulesAux_spec__4(v_k_4106_, v___x_4184_, v_sz_4186_, v___x_4187_, v___x_4185_);
                        crate::leanh::lean_dec_ref(v___x_4184_);
                        v_fst_4189_ = crate::leanh::lean_ctor_get(v___x_4188_, 0);
                        crate::leanh::lean_inc(v_fst_4189_);
                        crate::leanh::lean_dec_ref(v___x_4188_);
                        if crate::leanh::lean_obj_tag(v_fst_4189_) == 0 {
                            crate::leanh::lean_dec(v_pat_4169_);
                            crate::leanh::lean_dec_ref(v___x_4167_);
                            crate::leanh::lean_dec(v___x_4153_);
                            v___y_4136_ = v___y_4171_;
                            v___y_4137_ = v___y_4172_;
                            state = 5;
                            continue;
                        } else {
                            v_val_4190_ = crate::leanh::lean_ctor_get(v_fst_4189_, 0);
                            crate::leanh::lean_inc(v_val_4190_);
                            crate::leanh::lean_dec_ref_known(v_fst_4189_, 1);
                            if crate::leanh::lean_obj_tag(v_val_4190_) == 0 {
                                crate::leanh::lean_dec(v_pat_4169_);
                                crate::leanh::lean_dec_ref(v___x_4167_);
                                crate::leanh::lean_dec(v___x_4153_);
                                v___y_4136_ = v___y_4171_;
                                v___y_4137_ = v___y_4172_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_v_4115_);
                                v_val_4191_ = crate::leanh::lean_ctor_get(v_val_4190_, 0);
                                crate::leanh::lean_inc(v_val_4191_);
                                crate::leanh::lean_dec_ref_known(v_val_4190_, 1);
                                v___x_4192_ = l_Lean_Elab_Command_getRef___redArg(v___y_4171_);
                                if crate::leanh::lean_obj_tag(v___x_4192_) == 0 {
                                    v_a_4193_ = crate::leanh::lean_ctor_get(v___x_4192_, 0);
                                    crate::leanh::lean_inc(v_a_4193_);
                                    crate::leanh::lean_dec_ref_known(v___x_4192_, 1);
                                    v___x_4194_ =
                                        l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_4171_);
                                    if crate::leanh::lean_obj_tag(v___x_4194_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4194_, 1);
                                        v_quotContext_x3f_4195_ =
                                            crate::leanh::lean_ctor_get(v___y_4171_, 5);
                                        v_pat_4196_ = l_Lean_Syntax_setArg(
                                            v_pat_4169_,
                                            v___x_4147_,
                                            v_val_4191_,
                                        );
                                        v___x_4197_ =
                                            lean_array_set(v___x_4167_, v___x_4116_, v_pat_4196_);
                                        v___x_4198_ =
                                            l_Lean_SourceInfo_fromRef(v_a_4193_, v___x_4175_);
                                        crate::leanh::lean_dec(v_a_4193_);
                                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_4195_) == 0
                                        {
                                            v___x_4199_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_4172_);
                                            if crate::leanh::lean_obj_tag(v___x_4199_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_4199_, 1);
                                                v___y_4155_ = v___x_4197_;
                                                v___y_4156_ = v___x_4198_;
                                                state = 6;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec(v___x_4198_);
                                                crate::leanh::lean_dec_ref(v___x_4197_);
                                                crate::leanh::lean_dec(v___x_4153_);
                                                crate::leanh::lean_dec_ref(v_bs_x27_4117_);
                                                crate::leanh::lean_dec(v_k_4106_);
                                                v_a_4200_ =
                                                    crate::leanh::lean_ctor_get(v___x_4199_, 0);
                                                v_isSharedCheck_4207_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4199_))
                                                        as u8;
                                                if v_isSharedCheck_4207_ == 0 {
                                                    v___x_4202_ = v___x_4199_;
                                                    v_isShared_4203_ = v_isSharedCheck_4207_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4200_);
                                                    crate::leanh::lean_dec(v___x_4199_);
                                                    v___x_4202_ = crate::leanh::lean_box(0);
                                                    v_isShared_4203_ = v_isSharedCheck_4207_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v___y_4155_ = v___x_4197_;
                                            v___y_4156_ = v___x_4198_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_4193_);
                                        crate::leanh::lean_dec(v_val_4191_);
                                        crate::leanh::lean_dec(v_pat_4169_);
                                        crate::leanh::lean_dec_ref(v___x_4167_);
                                        crate::leanh::lean_dec(v___x_4153_);
                                        crate::leanh::lean_dec_ref(v_bs_x27_4117_);
                                        crate::leanh::lean_dec(v_k_4106_);
                                        v_a_4208_ = crate::leanh::lean_ctor_get(v___x_4194_, 0);
                                        v_isSharedCheck_4215_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4194_)) as u8;
                                        if v_isSharedCheck_4215_ == 0 {
                                            v___x_4210_ = v___x_4194_;
                                            v_isShared_4211_ = v_isSharedCheck_4215_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4208_);
                                            crate::leanh::lean_dec(v___x_4194_);
                                            v___x_4210_ = crate::leanh::lean_box(0);
                                            v_isShared_4211_ = v_isSharedCheck_4215_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_val_4191_);
                                    crate::leanh::lean_dec(v_pat_4169_);
                                    crate::leanh::lean_dec_ref(v___x_4167_);
                                    crate::leanh::lean_dec(v___x_4153_);
                                    crate::leanh::lean_dec_ref(v_bs_x27_4117_);
                                    crate::leanh::lean_dec(v_k_4106_);
                                    v_a_4216_ = crate::leanh::lean_ctor_get(v___x_4192_, 0);
                                    v_isSharedCheck_4223_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4192_)) as u8;
                                    if v_isSharedCheck_4223_ == 0 {
                                        v___x_4218_ = v___x_4192_;
                                        v_isShared_4219_ = v_isSharedCheck_4223_;
                                        state = 12;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4216_);
                                        crate::leanh::lean_dec(v___x_4192_);
                                        v___x_4218_ = crate::leanh::lean_box(0);
                                        v_isShared_4219_ = v_isSharedCheck_4223_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_x27_4174_);
                    crate::leanh::lean_dec(v_quoted_4173_);
                    crate::leanh::lean_dec(v_pat_4169_);
                    crate::leanh::lean_dec_ref(v___x_4167_);
                    crate::leanh::lean_dec(v___x_4153_);
                    v_a_4119_ = v_v_4115_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v_isShared_4203_ == 0 {
                    v___x_4205_ = v___x_4202_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4206_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4206_, 0, v_a_4200_);
                    v___x_4205_ = v_reuseFailAlloc_4206_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4205_;
            }
            10 => {
                if v_isShared_4211_ == 0 {
                    v___x_4213_ = v___x_4210_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4214_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
                    v___x_4213_ = v_reuseFailAlloc_4214_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4213_;
            }
            12 => {
                if v_isShared_4219_ == 0 {
                    v___x_4221_ = v___x_4218_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
                    v___x_4221_ = v_reuseFailAlloc_4222_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4221_;
            }
            14 => {
                if v_isShared_4229_ == 0 {
                    v___x_4231_ = v___x_4228_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
                    v___x_4231_ = v_reuseFailAlloc_4232_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___boxed(
    mut v_k_4234_: *mut crate::leanh::LeanObject,
    mut v_sz_4235_: *mut crate::leanh::LeanObject,
    mut v_i_4236_: *mut crate::leanh::LeanObject,
    mut v_bs_4237_: *mut crate::leanh::LeanObject,
    mut v___y_4238_: *mut crate::leanh::LeanObject,
    mut v___y_4239_: *mut crate::leanh::LeanObject,
    mut v___y_4240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4241_: usize = 0;
    let mut v_i_boxed_4242_: usize = 0;
    let mut v_res_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4241_ = crate::leanh::lean_unbox_usize(v_sz_4235_);
    crate::leanh::lean_dec(v_sz_4235_);
    v_i_boxed_4242_ = crate::leanh::lean_unbox_usize(v_i_4236_);
    crate::leanh::lean_dec(v_i_4236_);
    v_res_4243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_4234_, v_sz_boxed_4241_, v_i_boxed_4242_, v_bs_4237_, v___y_4238_, v___y_4239_);
    crate::leanh::lean_dec(v___y_4239_);
    crate::leanh::lean_dec_ref(v___y_4238_);
    return v_res_4243_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_Elab_Command_elabElabRulesAux___closed__4;
    v___x_4250_ = l_String_toRawSubstring_x27(v___x_4249_);
    return v___x_4250_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4255_ = l_Lean_Elab_Command_elabElabRulesAux___closed__8;
    v___x_4256_ = l_String_toRawSubstring_x27(v___x_4255_);
    return v___x_4256_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4262_ = l_Lean_Elab_Command_elabElabRulesAux___closed__14;
    v___x_4263_ = l_String_toRawSubstring_x27(v___x_4262_);
    return v___x_4263_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4275_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
    v___x_4276_ = l_String_toRawSubstring_x27(v___x_4275_);
    return v___x_4276_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4290_ = l_Lean_Elab_Command_elabElabRulesAux___closed__33;
    v___x_4291_ = l_String_toRawSubstring_x27(v___x_4290_);
    return v___x_4291_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = l_Lean_Elab_Command_elabElabRulesAux___closed__36;
    v___x_4295_ = l_String_toRawSubstring_x27(v___x_4294_);
    return v___x_4295_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4299_ = l_Lean_Elab_Command_elabElabRulesAux___closed__40;
    v___x_4300_ = l_String_toRawSubstring_x27(v___x_4299_);
    return v___x_4300_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4304_ = l_Lean_Elab_Command_elabElabRulesAux___closed__43;
    v___x_4305_ = l_String_toRawSubstring_x27(v___x_4304_);
    return v___x_4305_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4308_ = l_Lean_Elab_Command_elabElabRulesAux___closed__46;
    v___x_4309_ = l_String_toRawSubstring_x27(v___x_4308_);
    return v___x_4309_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4314_ = l_Lean_Elab_Command_elabElabRulesAux___closed__50;
    v___x_4315_ = l_String_toRawSubstring_x27(v___x_4314_);
    return v___x_4315_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4324_ = l_Lean_Elab_Command_elabElabRulesAux___closed__57;
    v___x_4325_ = l_Lean_stringToMessageData(v___x_4324_);
    return v___x_4325_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4327_ = l_Lean_Elab_Command_elabElabRulesAux___closed__59;
    v___x_4328_ = l_Lean_stringToMessageData(v___x_4327_);
    return v___x_4328_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4345_ = l_Lean_Elab_Command_elabElabRulesAux___closed__71;
    v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
    return v___x_4346_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4351_ = l_Lean_Elab_Command_elabElabRulesAux___closed__75;
    v___x_4352_ = l_Lean_stringToMessageData(v___x_4351_);
    return v___x_4352_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRulesAux(
    mut v_doc_x3f_4353_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_4354_: *mut crate::leanh::LeanObject,
    mut v_attrKind_4355_: *mut crate::leanh::LeanObject,
    mut v_k_4356_: *mut crate::leanh::LeanObject,
    mut v_cat_x3f_4357_: *mut crate::leanh::LeanObject,
    mut v_expty_x3f_4358_: *mut crate::leanh::LeanObject,
    mut v_alts_4359_: *mut crate::leanh::LeanObject,
    mut v_a_4360_: *mut crate::leanh::LeanObject,
    mut v_a_4361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4363_: usize = 0;
    let mut v___x_4364_: usize = 0;
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4369_: u8 = 0;
    let mut v___y_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v___x_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5157_: u8 = 0;
    let mut v___y_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5176_: u8 = 0;
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5180_: u8 = 0;
    let mut v_a_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5188_: u8 = 0;
    let mut v_catName_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5196_: u8 = 0;
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: u8 = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5220_: u8 = 0;
    let mut v___x_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5224_: u8 = 0;
    let mut v_a_5225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5228_: u8 = 0;
    let mut v___x_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5232_: u8 = 0;
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u8 = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5249_: u8 = 0;
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v_a_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5257_: u8 = 0;
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5261_: u8 = 0;
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: u8 = 0;
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: u8 = 0;
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: u8 = 0;
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: u8 = 0;
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: u8 = 0;
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5293_: u8 = 0;
    let mut v___x_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5297_: u8 = 0;
    let mut v_a_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5301_: u8 = 0;
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5305_: u8 = 0;
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5321_: u8 = 0;
    let mut v___x_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5325_: u8 = 0;
    let mut v_a_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5329_: u8 = 0;
    let mut v___x_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5333_: u8 = 0;
    let mut v___x_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: u8 = 0;
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5350_: u8 = 0;
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5354_: u8 = 0;
    let mut v_a_5355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut v_val_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5371_: u8 = 0;
    let mut v___x_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5375_: u8 = 0;
    let mut v_isSharedCheck_5376_: u8 = 0;
    let mut v_a_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5380_: u8 = 0;
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4363_ = lean_array_size(v_alts_4359_);
                v___x_4364_ = 0usize;
                crate::leanh::lean_inc(v_k_4356_);
                v___x_4365_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5(v_k_4356_, v_sz_4363_, v___x_4364_, v_alts_4359_, v_a_4360_, v_a_4361_);
                if crate::leanh::lean_obj_tag(v___x_4365_) == 0 {
                    v_a_4366_ = crate::leanh::lean_ctor_get(v___x_4365_, 0);
                    v_isSharedCheck_5376_ = (!crate::leanh::lean_is_exclusive(v___x_4365_)) as u8;
                    if v_isSharedCheck_5376_ == 0 {
                        v___x_4368_ = v___x_4365_;
                        v_isShared_4369_ = v_isSharedCheck_5376_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4366_);
                        crate::leanh::lean_dec(v___x_4365_);
                        v___x_4368_ = crate::leanh::lean_box(0);
                        v_isShared_4369_ = v_isSharedCheck_5376_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_expty_x3f_4358_);
                    crate::leanh::lean_dec(v_k_4356_);
                    crate::leanh::lean_dec(v_attrKind_4355_);
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v_a_5377_ = crate::leanh::lean_ctor_get(v___x_4365_, 0);
                    v_isSharedCheck_5384_ = (!crate::leanh::lean_is_exclusive(v___x_4365_)) as u8;
                    if v_isSharedCheck_5384_ == 0 {
                        v___x_5379_ = v___x_4365_;
                        v_isShared_5380_ = v_isSharedCheck_5384_;
                        state = 43;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5377_);
                        crate::leanh::lean_dec(v___x_4365_);
                        v___x_5379_ = crate::leanh::lean_box(0);
                        v_isShared_5380_ = v_isSharedCheck_5384_;
                        state = 43;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_cat_x3f_4357_) == 1 {
                    v_val_5363_ = crate::leanh::lean_ctor_get(v_cat_x3f_4357_, 0);
                    v___x_5364_ = l_Lean_TSyntax_getId(v_val_5363_);
                    v_catName_5190_ = v___x_5364_;
                    v___y_5191_ = v_a_4360_;
                    v___y_5192_ = v_a_4361_;
                    state = 20;
                    continue;
                } else {
                    if crate::leanh::lean_obj_tag(v_expty_x3f_4358_) == 1 {
                        v___x_5365_ = l_Lean_Elab_Command_elabElabRulesAux___closed__54;
                        v_catName_5190_ = v___x_5365_;
                        v___y_5191_ = v_a_4360_;
                        v___y_5192_ = v_a_4361_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_del_object(v___x_4368_);
                        crate::leanh::lean_dec(v_a_4366_);
                        crate::leanh::lean_dec(v_expty_x3f_4358_);
                        crate::leanh::lean_dec(v_k_4356_);
                        crate::leanh::lean_dec(v_attrKind_4355_);
                        crate::leanh::lean_dec(v_doc_x3f_4353_);
                        v___x_5366_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabElabRulesAux___closed__76
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Command_elabElabRulesAux___closed__76_once
                            ),
                            _init_l_Lean_Elab_Command_elabElabRulesAux___closed__76,
                        );
                        v___x_5367_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_5366_, v_a_4360_, v_a_4361_);
                        v_a_5368_ = crate::leanh::lean_ctor_get(v___x_5367_, 0);
                        v_isSharedCheck_5375_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5367_)) as u8;
                        if v_isSharedCheck_5375_ == 0 {
                            v___x_5370_ = v___x_5367_;
                            v_isShared_5371_ = v_isSharedCheck_5375_;
                            state = 41;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5368_);
                            crate::leanh::lean_dec(v___x_5367_);
                            v___x_5370_ = crate::leanh::lean_box(0);
                            v_isShared_5371_ = v_isSharedCheck_5375_;
                            state = 41;
                            continue;
                        }
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_4379_, 4);
                v___x_4383_ = l_Array_append___redArg(v___y_4379_, v___y_4382_);
                crate::leanh::lean_dec_ref(v___y_4382_);
                crate::leanh::lean_inc_n(v___y_4372_, 10);
                crate::leanh::lean_inc_n(v___y_4378_, 35);
                v___x_4384_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4384_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4384_, 1, v___y_4372_);
                crate::leanh::lean_ctor_set(v___x_4384_, 2, v___x_4383_);
                v___x_4385_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_4386_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_4387_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_4380_, 11);
                v___x_4388_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4387_);
                v___x_4389_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                v___x_4390_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4390_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4390_, 1, v___x_4389_);
                v___x_4391_ = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
                v___x_4392_ = l_Lean_Syntax_SepArray_ofElems(v___x_4391_, v___y_4376_);
                crate::leanh::lean_dec_ref(v___y_4376_);
                v___x_4393_ = l_Array_append___redArg(v___y_4379_, v___x_4392_);
                crate::leanh::lean_dec_ref(v___x_4392_);
                v___x_4394_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4394_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4394_, 1, v___y_4372_);
                crate::leanh::lean_ctor_set(v___x_4394_, 2, v___x_4393_);
                v___x_4395_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                v___x_4396_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4396_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4396_, 1, v___x_4395_);
                v___x_4397_ = l_Lean_Syntax_node3(
                    v___y_4378_,
                    v___x_4388_,
                    v___x_4390_,
                    v___x_4394_,
                    v___x_4396_,
                );
                v___x_4398_ = l_Lean_Syntax_node1(v___y_4378_, v___y_4372_, v___x_4397_);
                crate::leanh::lean_inc_ref(v___y_4373_);
                v___x_4399_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4399_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4399_, 1, v___y_4373_);
                v___x_4400_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5,
                );
                v___x_4401_ = l_Lean_Elab_Command_elabElabRulesAux___closed__6;
                crate::leanh::lean_inc_n(v___y_4377_, 3);
                crate::leanh::lean_inc_n(v___y_4381_, 3);
                v___x_4402_ = l_Lean_addMacroScope(v___y_4381_, v___x_4401_, v___y_4377_);
                v___x_4403_ = crate::leanh::lean_box(0);
                v___x_4404_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4404_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4404_, 1, v___x_4400_);
                crate::leanh::lean_ctor_set(v___x_4404_, 2, v___x_4402_);
                crate::leanh::lean_ctor_set(v___x_4404_, 3, v___x_4403_);
                v___x_4405_ = lean_mk_syntax_ident(v_k_4356_);
                v___x_4406_ =
                    l_Lean_Syntax_node2(v___y_4378_, v___y_4372_, v___x_4404_, v___x_4405_);
                v___x_4407_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_4408_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4408_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4408_, 1, v___x_4407_);
                v___x_4409_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__9_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9,
                );
                v___x_4410_ = l_Lean_Elab_Command_elabElabRulesAux___closed__10;
                crate::leanh::lean_inc_ref_n(v___y_4375_, 2);
                v___x_4411_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___y_4375_, v___x_4386_, v___x_4410_);
                crate::leanh::lean_inc(v___x_4411_);
                v___x_4412_ = l_Lean_addMacroScope(v___y_4381_, v___x_4411_, v___y_4377_);
                v___x_4413_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4413_, 0, v___x_4411_);
                crate::leanh::lean_ctor_set(v___x_4413_, 1, v___x_4403_);
                v___x_4414_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4414_, 0, v___x_4413_);
                crate::leanh::lean_ctor_set(v___x_4414_, 1, v___x_4403_);
                v___x_4415_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4415_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4415_, 1, v___x_4409_);
                crate::leanh::lean_ctor_set(v___x_4415_, 2, v___x_4412_);
                crate::leanh::lean_ctor_set(v___x_4415_, 3, v___x_4414_);
                v___x_4416_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_4417_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4417_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4417_, 1, v___x_4416_);
                v___x_4418_ = l_Lean_Elab_Command_elabElabRulesAux___closed__12;
                v___x_4419_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4418_);
                v___x_4420_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4420_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4420_, 1, v___x_4418_);
                v___x_4421_ = l_Lean_Elab_Command_elabElabRulesAux___closed__13;
                v___x_4422_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4421_);
                v___x_4423_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15,
                );
                v___x_4424_ = l_Lean_Elab_Command_elabElabRulesAux___closed__16;
                v___x_4425_ = l_Lean_addMacroScope(v___y_4381_, v___x_4424_, v___y_4377_);
                v___x_4426_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4426_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4426_, 1, v___x_4423_);
                crate::leanh::lean_ctor_set(v___x_4426_, 2, v___x_4425_);
                crate::leanh::lean_ctor_set(v___x_4426_, 3, v___x_4403_);
                v___x_4427_ = l_Lean_Elab_Command_elabElabRulesAux___closed__17;
                v___x_4428_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4427_);
                v___x_4429_ = l_Lean_Elab_Command_elabElabRulesAux___closed__18;
                v___x_4430_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4430_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4430_, 1, v___x_4429_);
                v___x_4431_ = l_Lean_Syntax_node1(v___y_4378_, v___x_4428_, v___x_4430_);
                crate::leanh::lean_inc(v___x_4431_);
                crate::leanh::lean_inc_ref(v___x_4426_);
                v___x_4432_ =
                    l_Lean_Syntax_node2(v___y_4378_, v___y_4372_, v___x_4426_, v___x_4431_);
                v___x_4433_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4433_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4433_, 1, v___y_4372_);
                crate::leanh::lean_ctor_set(v___x_4433_, 2, v___y_4379_);
                v___x_4434_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_4435_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4435_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4435_, 1, v___x_4434_);
                v___x_4436_ = l_Lean_Elab_Command_elabElabRulesAux___closed__19;
                v___x_4437_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4436_);
                v___x_4438_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4438_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4438_, 1, v___x_4436_);
                v___x_4439_ = l_Lean_Elab_Command_elabElabRulesAux___closed__20;
                v___x_4440_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4439_);
                crate::leanh::lean_inc_ref_n(v___x_4433_, 3);
                v___x_4441_ =
                    l_Lean_Syntax_node2(v___y_4378_, v___x_4440_, v___x_4433_, v___x_4426_);
                v___x_4442_ = l_Lean_Syntax_node1(v___y_4378_, v___y_4372_, v___x_4441_);
                v___x_4443_ = l_Lean_Elab_Command_elabElabRulesAux___closed__21;
                v___x_4444_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4444_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4444_, 1, v___x_4443_);
                v___x_4445_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                v___x_4446_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4445_);
                v___x_4447_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_4448_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4447_);
                v___x_4449_ = l_Array_append___redArg(v___y_4379_, v_a_4366_);
                crate::leanh::lean_dec(v_a_4366_);
                v___x_4450_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_4451_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4451_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4451_, 1, v___x_4450_);
                v___x_4452_ = l_Lean_Syntax_node1(v___y_4378_, v___y_4372_, v___x_4431_);
                v___x_4453_ = l_Lean_Syntax_node1(v___y_4378_, v___y_4372_, v___x_4452_);
                v___x_4454_ = l_Lean_Elab_Command_elabElabRulesAux___closed__23;
                v___x_4455_ =
                    l_Lean_Name_mkStr4(v___y_4380_, v___x_4385_, v___x_4386_, v___x_4454_);
                v___x_4456_ = l_Lean_Elab_Command_elabElabRulesAux___closed__24;
                v___x_4457_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4457_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4457_, 1, v___x_4456_);
                v___x_4458_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
                v___x_4459_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26,
                );
                v___x_4460_ = l_Lean_Elab_Command_elabElabRulesAux___closed__27;
                v___x_4461_ = l_Lean_addMacroScope(v___y_4381_, v___x_4460_, v___y_4377_);
                v___x_4462_ = l_Lean_Name_mkStr3(v___y_4380_, v___y_4375_, v___x_4458_);
                v___x_4463_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4463_, 0, v___x_4462_);
                crate::leanh::lean_ctor_set(v___x_4463_, 1, v___x_4403_);
                v___x_4464_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4464_, 0, v___x_4463_);
                crate::leanh::lean_ctor_set(v___x_4464_, 1, v___x_4403_);
                v___x_4465_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4465_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4465_, 1, v___x_4459_);
                crate::leanh::lean_ctor_set(v___x_4465_, 2, v___x_4461_);
                crate::leanh::lean_ctor_set(v___x_4465_, 3, v___x_4464_);
                v___x_4466_ =
                    l_Lean_Syntax_node2(v___y_4378_, v___x_4455_, v___x_4457_, v___x_4465_);
                crate::leanh::lean_inc_ref(v___x_4435_);
                v___x_4467_ = l_Lean_Syntax_node4(
                    v___y_4378_,
                    v___x_4448_,
                    v___x_4451_,
                    v___x_4453_,
                    v___x_4435_,
                    v___x_4466_,
                );
                v___x_4468_ = lean_array_push(v___x_4449_, v___x_4467_);
                v___x_4469_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4469_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4469_, 1, v___y_4372_);
                crate::leanh::lean_ctor_set(v___x_4469_, 2, v___x_4468_);
                v___x_4470_ = l_Lean_Syntax_node1(v___y_4378_, v___x_4446_, v___x_4469_);
                v___x_4471_ = l_Lean_Syntax_node6(
                    v___y_4378_,
                    v___x_4437_,
                    v___x_4438_,
                    v___x_4433_,
                    v___x_4433_,
                    v___x_4442_,
                    v___x_4444_,
                    v___x_4470_,
                );
                v___x_4472_ = l_Lean_Syntax_node4(
                    v___y_4378_,
                    v___x_4422_,
                    v___x_4432_,
                    v___x_4433_,
                    v___x_4435_,
                    v___x_4471_,
                );
                v___x_4473_ =
                    l_Lean_Syntax_node2(v___y_4378_, v___x_4419_, v___x_4420_, v___x_4472_);
                v___x_4474_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_4475_ = lean_mk_empty_array_with_capacity(v___x_4474_);
                v___x_4476_ = lean_array_push(v___x_4475_, v___x_4384_);
                v___x_4477_ = lean_array_push(v___x_4476_, v___x_4398_);
                v___x_4478_ = lean_array_push(v___x_4477_, v___y_4374_);
                v___x_4479_ = lean_array_push(v___x_4478_, v___x_4399_);
                v___x_4480_ = lean_array_push(v___x_4479_, v___x_4406_);
                v___x_4481_ = lean_array_push(v___x_4480_, v___x_4408_);
                v___x_4482_ = lean_array_push(v___x_4481_, v___x_4415_);
                v___x_4483_ = lean_array_push(v___x_4482_, v___x_4417_);
                v___x_4484_ = lean_array_push(v___x_4483_, v___x_4473_);
                crate::leanh::lean_inc(v___y_4371_);
                v___x_4485_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4485_, 0, v___y_4378_);
                crate::leanh::lean_ctor_set(v___x_4485_, 1, v___y_4371_);
                crate::leanh::lean_ctor_set(v___x_4485_, 2, v___x_4484_);
                if v_isShared_4369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4368_, 0, v___x_4485_);
                    v___x_4487_ = v___x_4368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4488_, 0, v___x_4485_);
                    v___x_4487_ = v_reuseFailAlloc_4488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4487_;
            }
            4 => {
                v___x_4495_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_4496_ = l_Lean_Elab_Command_elabElabRulesAux___closed__28;
                v___x_4497_ = l_Lean_Elab_Command_elabElabRulesAux___closed__30;
                v___x_4498_ = l_Lean_Elab_Command_elabElabRulesAux___closed__31;
                v___x_4499_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_4500_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_4353_) == 1 {
                    v_val_4501_ = crate::leanh::lean_ctor_get(v_doc_x3f_4353_, 0);
                    crate::leanh::lean_inc(v_val_4501_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_4353_, 1);
                    v___x_4502_ = l_Array_mkArray1___redArg(v_val_4501_);
                    v___y_4371_ = v___x_4498_;
                    v___y_4372_ = v___x_4499_;
                    v___y_4373_ = v___x_4497_;
                    v___y_4374_ = v___y_4490_;
                    v___y_4375_ = v___x_4496_;
                    v___y_4376_ = v___y_4491_;
                    v___y_4377_ = v___y_4492_;
                    v___y_4378_ = v___y_4493_;
                    v___y_4379_ = v___x_4500_;
                    v___y_4380_ = v___x_4495_;
                    v___y_4381_ = v_a_4494_;
                    v___y_4382_ = v___x_4502_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v___x_4503_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_4371_ = v___x_4498_;
                    v___y_4372_ = v___x_4499_;
                    v___y_4373_ = v___x_4497_;
                    v___y_4374_ = v___y_4490_;
                    v___y_4375_ = v___x_4496_;
                    v___y_4376_ = v___y_4491_;
                    v___y_4377_ = v___y_4492_;
                    v___y_4378_ = v___y_4493_;
                    v___y_4379_ = v___x_4500_;
                    v___y_4380_ = v___x_4495_;
                    v___y_4381_ = v_a_4494_;
                    v___y_4382_ = v___x_4503_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_4512_, 3);
                v___x_4518_ = l_Array_append___redArg(v___y_4512_, v___y_4517_);
                crate::leanh::lean_dec_ref(v___y_4517_);
                crate::leanh::lean_inc_n(v___y_4505_, 7);
                crate::leanh::lean_inc_n(v___y_4509_, 26);
                v___x_4519_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4519_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4519_, 1, v___y_4505_);
                crate::leanh::lean_ctor_set(v___x_4519_, 2, v___x_4518_);
                v___x_4520_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_4521_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_4522_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_4507_, 8);
                v___x_4523_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___x_4520_, v___x_4521_, v___x_4522_);
                v___x_4524_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                v___x_4525_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4525_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4525_, 1, v___x_4524_);
                v___x_4526_ = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
                v___x_4527_ = l_Lean_Syntax_SepArray_ofElems(v___x_4526_, v___y_4515_);
                crate::leanh::lean_dec_ref(v___y_4515_);
                v___x_4528_ = l_Array_append___redArg(v___y_4512_, v___x_4527_);
                crate::leanh::lean_dec_ref(v___x_4527_);
                v___x_4529_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4529_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4529_, 1, v___y_4505_);
                crate::leanh::lean_ctor_set(v___x_4529_, 2, v___x_4528_);
                v___x_4530_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                v___x_4531_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4531_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4531_, 1, v___x_4530_);
                v___x_4532_ = l_Lean_Syntax_node3(
                    v___y_4509_,
                    v___x_4523_,
                    v___x_4525_,
                    v___x_4529_,
                    v___x_4531_,
                );
                v___x_4533_ = l_Lean_Syntax_node1(v___y_4509_, v___y_4505_, v___x_4532_);
                crate::leanh::lean_inc_ref(v___y_4513_);
                v___x_4534_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4534_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4534_, 1, v___y_4513_);
                v___x_4535_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5,
                );
                v___x_4536_ = l_Lean_Elab_Command_elabElabRulesAux___closed__6;
                crate::leanh::lean_inc_n(v___y_4514_, 2);
                crate::leanh::lean_inc_n(v___y_4506_, 2);
                v___x_4537_ = l_Lean_addMacroScope(v___y_4506_, v___x_4536_, v___y_4514_);
                v___x_4538_ = crate::leanh::lean_box(0);
                v___x_4539_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4539_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4539_, 1, v___x_4535_);
                crate::leanh::lean_ctor_set(v___x_4539_, 2, v___x_4537_);
                crate::leanh::lean_ctor_set(v___x_4539_, 3, v___x_4538_);
                v___x_4540_ = lean_mk_syntax_ident(v_k_4356_);
                v___x_4541_ =
                    l_Lean_Syntax_node2(v___y_4509_, v___y_4505_, v___x_4539_, v___x_4540_);
                v___x_4542_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_4543_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4543_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4543_, 1, v___x_4542_);
                v___x_4544_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__34),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__34_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__34,
                );
                v___x_4545_ = l_Lean_Elab_Command_elabElabRulesAux___closed__35;
                crate::leanh::lean_inc_ref(v___y_4516_);
                crate::leanh::lean_inc_ref_n(v___y_4508_, 2);
                v___x_4546_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___y_4508_, v___y_4516_, v___x_4545_);
                crate::leanh::lean_inc(v___x_4546_);
                v___x_4547_ = l_Lean_addMacroScope(v___y_4506_, v___x_4546_, v___y_4514_);
                v___x_4548_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4548_, 0, v___x_4546_);
                crate::leanh::lean_ctor_set(v___x_4548_, 1, v___x_4538_);
                v___x_4549_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4549_, 0, v___x_4548_);
                crate::leanh::lean_ctor_set(v___x_4549_, 1, v___x_4538_);
                v___x_4550_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4550_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4550_, 1, v___x_4544_);
                crate::leanh::lean_ctor_set(v___x_4550_, 2, v___x_4547_);
                crate::leanh::lean_ctor_set(v___x_4550_, 3, v___x_4549_);
                v___x_4551_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_4552_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4552_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4552_, 1, v___x_4551_);
                v___x_4553_ = l_Lean_Elab_Command_elabElabRulesAux___closed__12;
                v___x_4554_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___x_4520_, v___x_4521_, v___x_4553_);
                v___x_4555_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4555_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4555_, 1, v___x_4553_);
                v___x_4556_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                v___x_4557_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___x_4520_, v___x_4521_, v___x_4556_);
                v___x_4558_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_4559_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___x_4520_, v___x_4521_, v___x_4558_);
                v___x_4560_ = l_Array_append___redArg(v___y_4512_, v_a_4366_);
                crate::leanh::lean_dec(v_a_4366_);
                v___x_4561_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_4562_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4562_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4562_, 1, v___x_4561_);
                v___x_4563_ = l_Lean_Elab_Command_elabElabRulesAux___closed__17;
                v___x_4564_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___x_4520_, v___x_4521_, v___x_4563_);
                v___x_4565_ = l_Lean_Elab_Command_elabElabRulesAux___closed__18;
                v___x_4566_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4566_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4566_, 1, v___x_4565_);
                v___x_4567_ = l_Lean_Syntax_node1(v___y_4509_, v___x_4564_, v___x_4566_);
                v___x_4568_ = l_Lean_Syntax_node1(v___y_4509_, v___y_4505_, v___x_4567_);
                v___x_4569_ = l_Lean_Syntax_node1(v___y_4509_, v___y_4505_, v___x_4568_);
                v___x_4570_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_4571_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4571_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4571_, 1, v___x_4570_);
                v___x_4572_ = l_Lean_Elab_Command_elabElabRulesAux___closed__23;
                v___x_4573_ =
                    l_Lean_Name_mkStr4(v___y_4507_, v___x_4520_, v___x_4521_, v___x_4572_);
                v___x_4574_ = l_Lean_Elab_Command_elabElabRulesAux___closed__24;
                v___x_4575_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4575_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4575_, 1, v___x_4574_);
                v___x_4576_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
                v___x_4577_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26,
                );
                v___x_4578_ = l_Lean_Elab_Command_elabElabRulesAux___closed__27;
                v___x_4579_ = l_Lean_addMacroScope(v___y_4506_, v___x_4578_, v___y_4514_);
                v___x_4580_ = l_Lean_Name_mkStr3(v___y_4507_, v___y_4508_, v___x_4576_);
                v___x_4581_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4581_, 0, v___x_4580_);
                crate::leanh::lean_ctor_set(v___x_4581_, 1, v___x_4538_);
                v___x_4582_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4582_, 0, v___x_4581_);
                crate::leanh::lean_ctor_set(v___x_4582_, 1, v___x_4538_);
                v___x_4583_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4583_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4583_, 1, v___x_4577_);
                crate::leanh::lean_ctor_set(v___x_4583_, 2, v___x_4579_);
                crate::leanh::lean_ctor_set(v___x_4583_, 3, v___x_4582_);
                v___x_4584_ =
                    l_Lean_Syntax_node2(v___y_4509_, v___x_4573_, v___x_4575_, v___x_4583_);
                v___x_4585_ = l_Lean_Syntax_node4(
                    v___y_4509_,
                    v___x_4559_,
                    v___x_4562_,
                    v___x_4569_,
                    v___x_4571_,
                    v___x_4584_,
                );
                v___x_4586_ = lean_array_push(v___x_4560_, v___x_4585_);
                v___x_4587_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4587_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4587_, 1, v___y_4505_);
                crate::leanh::lean_ctor_set(v___x_4587_, 2, v___x_4586_);
                v___x_4588_ = l_Lean_Syntax_node1(v___y_4509_, v___x_4557_, v___x_4587_);
                v___x_4589_ =
                    l_Lean_Syntax_node2(v___y_4509_, v___x_4554_, v___x_4555_, v___x_4588_);
                v___x_4590_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_4591_ = lean_mk_empty_array_with_capacity(v___x_4590_);
                v___x_4592_ = lean_array_push(v___x_4591_, v___x_4519_);
                v___x_4593_ = lean_array_push(v___x_4592_, v___x_4533_);
                v___x_4594_ = lean_array_push(v___x_4593_, v___y_4511_);
                v___x_4595_ = lean_array_push(v___x_4594_, v___x_4534_);
                v___x_4596_ = lean_array_push(v___x_4595_, v___x_4541_);
                v___x_4597_ = lean_array_push(v___x_4596_, v___x_4543_);
                v___x_4598_ = lean_array_push(v___x_4597_, v___x_4550_);
                v___x_4599_ = lean_array_push(v___x_4598_, v___x_4552_);
                v___x_4600_ = lean_array_push(v___x_4599_, v___x_4589_);
                crate::leanh::lean_inc(v___y_4510_);
                v___x_4601_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4601_, 0, v___y_4509_);
                crate::leanh::lean_ctor_set(v___x_4601_, 1, v___y_4510_);
                crate::leanh::lean_ctor_set(v___x_4601_, 2, v___x_4600_);
                v___x_4602_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4602_, 0, v___x_4601_);
                return v___x_4602_;
            }
            6 => {
                v___x_4609_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_4610_ = l_Lean_Elab_Command_elabElabRulesAux___closed__28;
                v___x_4611_ = l_Lean_Elab_Command_elabElabRulesAux___closed__29;
                v___x_4612_ = l_Lean_Elab_Command_elabElabRulesAux___closed__30;
                v___x_4613_ = l_Lean_Elab_Command_elabElabRulesAux___closed__31;
                v___x_4614_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_4615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_4353_) == 1 {
                    v_val_4616_ = crate::leanh::lean_ctor_get(v_doc_x3f_4353_, 0);
                    crate::leanh::lean_inc(v_val_4616_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_4353_, 1);
                    v___x_4617_ = l_Array_mkArray1___redArg(v_val_4616_);
                    v___y_4505_ = v___x_4614_;
                    v___y_4506_ = v_a_4608_;
                    v___y_4507_ = v___x_4609_;
                    v___y_4508_ = v___x_4610_;
                    v___y_4509_ = v___y_4604_;
                    v___y_4510_ = v___x_4613_;
                    v___y_4511_ = v___y_4605_;
                    v___y_4512_ = v___x_4615_;
                    v___y_4513_ = v___x_4612_;
                    v___y_4514_ = v___y_4606_;
                    v___y_4515_ = v___y_4607_;
                    v___y_4516_ = v___x_4611_;
                    v___y_4517_ = v___x_4617_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v___x_4618_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_4505_ = v___x_4614_;
                    v___y_4506_ = v_a_4608_;
                    v___y_4507_ = v___x_4609_;
                    v___y_4508_ = v___x_4610_;
                    v___y_4509_ = v___y_4604_;
                    v___y_4510_ = v___x_4613_;
                    v___y_4511_ = v___y_4605_;
                    v___y_4512_ = v___x_4615_;
                    v___y_4513_ = v___x_4612_;
                    v___y_4514_ = v___y_4606_;
                    v___y_4515_ = v___y_4607_;
                    v___y_4516_ = v___x_4611_;
                    v___y_4517_ = v___x_4618_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref_n(v___y_4629_, 4);
                v___x_4632_ = l_Array_append___redArg(v___y_4629_, v___y_4631_);
                crate::leanh::lean_dec_ref(v___y_4631_);
                crate::leanh::lean_inc_n(v___y_4627_, 10);
                crate::leanh::lean_inc_n(v___y_4623_, 36);
                v___x_4633_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4633_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4633_, 1, v___y_4627_);
                crate::leanh::lean_ctor_set(v___x_4633_, 2, v___x_4632_);
                v___x_4634_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_4635_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_4636_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_4625_, 11);
                v___x_4637_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4636_);
                v___x_4638_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                v___x_4639_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4639_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4639_, 1, v___x_4638_);
                v___x_4640_ = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
                v___x_4641_ = l_Lean_Syntax_SepArray_ofElems(v___x_4640_, v___y_4628_);
                crate::leanh::lean_dec_ref(v___y_4628_);
                v___x_4642_ = l_Array_append___redArg(v___y_4629_, v___x_4641_);
                crate::leanh::lean_dec_ref(v___x_4641_);
                v___x_4643_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4643_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4643_, 1, v___y_4627_);
                crate::leanh::lean_ctor_set(v___x_4643_, 2, v___x_4642_);
                v___x_4644_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                v___x_4645_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4645_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4645_, 1, v___x_4644_);
                v___x_4646_ = l_Lean_Syntax_node3(
                    v___y_4623_,
                    v___x_4637_,
                    v___x_4639_,
                    v___x_4643_,
                    v___x_4645_,
                );
                v___x_4647_ = l_Lean_Syntax_node1(v___y_4623_, v___y_4627_, v___x_4646_);
                crate::leanh::lean_inc_ref(v___y_4624_);
                v___x_4648_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4648_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4648_, 1, v___y_4624_);
                v___x_4649_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5,
                );
                v___x_4650_ = l_Lean_Elab_Command_elabElabRulesAux___closed__6;
                crate::leanh::lean_inc_n(v___y_4630_, 4);
                crate::leanh::lean_inc_n(v___y_4622_, 4);
                v___x_4651_ = l_Lean_addMacroScope(v___y_4622_, v___x_4650_, v___y_4630_);
                v___x_4652_ = crate::leanh::lean_box(0);
                v___x_4653_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4653_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4653_, 1, v___x_4649_);
                crate::leanh::lean_ctor_set(v___x_4653_, 2, v___x_4651_);
                crate::leanh::lean_ctor_set(v___x_4653_, 3, v___x_4652_);
                v___x_4654_ = lean_mk_syntax_ident(v_k_4356_);
                v___x_4655_ =
                    l_Lean_Syntax_node2(v___y_4623_, v___y_4627_, v___x_4653_, v___x_4654_);
                v___x_4656_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_4657_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4657_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4657_, 1, v___x_4656_);
                v___x_4658_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__37),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__37_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37,
                );
                v___x_4659_ = l_Lean_Elab_Command_elabElabRulesAux___closed__38;
                v___x_4660_ = l_Lean_Elab_Command_elabElabRulesAux___closed__39;
                crate::leanh::lean_inc_ref_n(v___y_4620_, 2);
                v___x_4661_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___y_4620_, v___x_4659_, v___x_4660_);
                crate::leanh::lean_inc(v___x_4661_);
                v___x_4662_ = l_Lean_addMacroScope(v___y_4622_, v___x_4661_, v___y_4630_);
                v___x_4663_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4663_, 0, v___x_4661_);
                crate::leanh::lean_ctor_set(v___x_4663_, 1, v___x_4652_);
                v___x_4664_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4664_, 0, v___x_4663_);
                crate::leanh::lean_ctor_set(v___x_4664_, 1, v___x_4652_);
                v___x_4665_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4665_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4665_, 1, v___x_4658_);
                crate::leanh::lean_ctor_set(v___x_4665_, 2, v___x_4662_);
                crate::leanh::lean_ctor_set(v___x_4665_, 3, v___x_4664_);
                v___x_4666_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_4667_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4667_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4667_, 1, v___x_4666_);
                v___x_4668_ = l_Lean_Elab_Command_elabElabRulesAux___closed__12;
                v___x_4669_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4668_);
                v___x_4670_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4670_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4670_, 1, v___x_4668_);
                v___x_4671_ = l_Lean_Elab_Command_elabElabRulesAux___closed__13;
                v___x_4672_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4671_);
                v___x_4673_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15,
                );
                v___x_4674_ = l_Lean_Elab_Command_elabElabRulesAux___closed__16;
                v___x_4675_ = l_Lean_addMacroScope(v___y_4622_, v___x_4674_, v___y_4630_);
                v___x_4676_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4676_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4676_, 1, v___x_4673_);
                crate::leanh::lean_ctor_set(v___x_4676_, 2, v___x_4675_);
                crate::leanh::lean_ctor_set(v___x_4676_, 3, v___x_4652_);
                v___x_4677_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__41),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__41_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__41,
                );
                v___x_4678_ = l_Lean_Elab_Command_elabElabRulesAux___closed__42;
                v___x_4679_ = l_Lean_addMacroScope(v___y_4622_, v___x_4678_, v___y_4630_);
                v___x_4680_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4680_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4680_, 1, v___x_4677_);
                crate::leanh::lean_ctor_set(v___x_4680_, 2, v___x_4679_);
                crate::leanh::lean_ctor_set(v___x_4680_, 3, v___x_4652_);
                crate::leanh::lean_inc_ref(v___x_4676_);
                v___x_4681_ =
                    l_Lean_Syntax_node2(v___y_4623_, v___y_4627_, v___x_4676_, v___x_4680_);
                v___x_4682_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4682_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4682_, 1, v___y_4627_);
                crate::leanh::lean_ctor_set(v___x_4682_, 2, v___y_4629_);
                v___x_4683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_4684_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4684_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4684_, 1, v___x_4683_);
                v___x_4685_ = l_Lean_Elab_Command_elabElabRulesAux___closed__19;
                v___x_4686_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4685_);
                v___x_4687_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4687_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4687_, 1, v___x_4685_);
                v___x_4688_ = l_Lean_Elab_Command_elabElabRulesAux___closed__20;
                v___x_4689_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4688_);
                crate::leanh::lean_inc_ref_n(v___x_4682_, 3);
                v___x_4690_ =
                    l_Lean_Syntax_node2(v___y_4623_, v___x_4689_, v___x_4682_, v___x_4676_);
                v___x_4691_ = l_Lean_Syntax_node1(v___y_4623_, v___y_4627_, v___x_4690_);
                v___x_4692_ = l_Lean_Elab_Command_elabElabRulesAux___closed__21;
                v___x_4693_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4693_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4693_, 1, v___x_4692_);
                v___x_4694_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                v___x_4695_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4694_);
                v___x_4696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_4697_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4696_);
                v___x_4698_ = l_Array_append___redArg(v___y_4629_, v_a_4366_);
                crate::leanh::lean_dec(v_a_4366_);
                v___x_4699_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_4700_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4700_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4700_, 1, v___x_4699_);
                v___x_4701_ = l_Lean_Elab_Command_elabElabRulesAux___closed__17;
                v___x_4702_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4701_);
                v___x_4703_ = l_Lean_Elab_Command_elabElabRulesAux___closed__18;
                v___x_4704_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4704_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4704_, 1, v___x_4703_);
                v___x_4705_ = l_Lean_Syntax_node1(v___y_4623_, v___x_4702_, v___x_4704_);
                v___x_4706_ = l_Lean_Syntax_node1(v___y_4623_, v___y_4627_, v___x_4705_);
                v___x_4707_ = l_Lean_Syntax_node1(v___y_4623_, v___y_4627_, v___x_4706_);
                v___x_4708_ = l_Lean_Elab_Command_elabElabRulesAux___closed__23;
                v___x_4709_ =
                    l_Lean_Name_mkStr4(v___y_4625_, v___x_4634_, v___x_4635_, v___x_4708_);
                v___x_4710_ = l_Lean_Elab_Command_elabElabRulesAux___closed__24;
                v___x_4711_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4711_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4711_, 1, v___x_4710_);
                v___x_4712_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
                v___x_4713_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26,
                );
                v___x_4714_ = l_Lean_Elab_Command_elabElabRulesAux___closed__27;
                v___x_4715_ = l_Lean_addMacroScope(v___y_4622_, v___x_4714_, v___y_4630_);
                v___x_4716_ = l_Lean_Name_mkStr3(v___y_4625_, v___y_4620_, v___x_4712_);
                v___x_4717_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4717_, 0, v___x_4716_);
                crate::leanh::lean_ctor_set(v___x_4717_, 1, v___x_4652_);
                v___x_4718_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4718_, 0, v___x_4717_);
                crate::leanh::lean_ctor_set(v___x_4718_, 1, v___x_4652_);
                v___x_4719_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4719_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4719_, 1, v___x_4713_);
                crate::leanh::lean_ctor_set(v___x_4719_, 2, v___x_4715_);
                crate::leanh::lean_ctor_set(v___x_4719_, 3, v___x_4718_);
                v___x_4720_ =
                    l_Lean_Syntax_node2(v___y_4623_, v___x_4709_, v___x_4711_, v___x_4719_);
                crate::leanh::lean_inc_ref(v___x_4684_);
                v___x_4721_ = l_Lean_Syntax_node4(
                    v___y_4623_,
                    v___x_4697_,
                    v___x_4700_,
                    v___x_4707_,
                    v___x_4684_,
                    v___x_4720_,
                );
                v___x_4722_ = lean_array_push(v___x_4698_, v___x_4721_);
                v___x_4723_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4723_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4723_, 1, v___y_4627_);
                crate::leanh::lean_ctor_set(v___x_4723_, 2, v___x_4722_);
                v___x_4724_ = l_Lean_Syntax_node1(v___y_4623_, v___x_4695_, v___x_4723_);
                v___x_4725_ = l_Lean_Syntax_node6(
                    v___y_4623_,
                    v___x_4686_,
                    v___x_4687_,
                    v___x_4682_,
                    v___x_4682_,
                    v___x_4691_,
                    v___x_4693_,
                    v___x_4724_,
                );
                v___x_4726_ = l_Lean_Syntax_node4(
                    v___y_4623_,
                    v___x_4672_,
                    v___x_4681_,
                    v___x_4682_,
                    v___x_4684_,
                    v___x_4725_,
                );
                v___x_4727_ =
                    l_Lean_Syntax_node2(v___y_4623_, v___x_4669_, v___x_4670_, v___x_4726_);
                v___x_4728_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_4729_ = lean_mk_empty_array_with_capacity(v___x_4728_);
                v___x_4730_ = lean_array_push(v___x_4729_, v___x_4633_);
                v___x_4731_ = lean_array_push(v___x_4730_, v___x_4647_);
                v___x_4732_ = lean_array_push(v___x_4731_, v___y_4626_);
                v___x_4733_ = lean_array_push(v___x_4732_, v___x_4648_);
                v___x_4734_ = lean_array_push(v___x_4733_, v___x_4655_);
                v___x_4735_ = lean_array_push(v___x_4734_, v___x_4657_);
                v___x_4736_ = lean_array_push(v___x_4735_, v___x_4665_);
                v___x_4737_ = lean_array_push(v___x_4736_, v___x_4667_);
                v___x_4738_ = lean_array_push(v___x_4737_, v___x_4727_);
                crate::leanh::lean_inc(v___y_4621_);
                v___x_4739_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4739_, 0, v___y_4623_);
                crate::leanh::lean_ctor_set(v___x_4739_, 1, v___y_4621_);
                crate::leanh::lean_ctor_set(v___x_4739_, 2, v___x_4738_);
                v___x_4740_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4740_, 0, v___x_4739_);
                return v___x_4740_;
            }
            8 => {
                v___x_4747_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_4748_ = l_Lean_Elab_Command_elabElabRulesAux___closed__28;
                v___x_4749_ = l_Lean_Elab_Command_elabElabRulesAux___closed__30;
                v___x_4750_ = l_Lean_Elab_Command_elabElabRulesAux___closed__31;
                v___x_4751_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_4752_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_4353_) == 1 {
                    v_val_4753_ = crate::leanh::lean_ctor_get(v_doc_x3f_4353_, 0);
                    crate::leanh::lean_inc(v_val_4753_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_4353_, 1);
                    v___x_4754_ = l_Array_mkArray1___redArg(v_val_4753_);
                    v___y_4620_ = v___x_4748_;
                    v___y_4621_ = v___x_4750_;
                    v___y_4622_ = v_a_4746_;
                    v___y_4623_ = v___y_4742_;
                    v___y_4624_ = v___x_4749_;
                    v___y_4625_ = v___x_4747_;
                    v___y_4626_ = v___y_4743_;
                    v___y_4627_ = v___x_4751_;
                    v___y_4628_ = v___y_4744_;
                    v___y_4629_ = v___x_4752_;
                    v___y_4630_ = v___y_4745_;
                    v___y_4631_ = v___x_4754_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v___x_4755_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_4620_ = v___x_4748_;
                    v___y_4621_ = v___x_4750_;
                    v___y_4622_ = v_a_4746_;
                    v___y_4623_ = v___y_4742_;
                    v___y_4624_ = v___x_4749_;
                    v___y_4625_ = v___x_4747_;
                    v___y_4626_ = v___y_4743_;
                    v___y_4627_ = v___x_4751_;
                    v___y_4628_ = v___y_4744_;
                    v___y_4629_ = v___x_4752_;
                    v___y_4630_ = v___y_4745_;
                    v___y_4631_ = v___x_4755_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                crate::leanh::lean_inc_ref_n(v___y_4765_, 3);
                v___x_4769_ = l_Array_append___redArg(v___y_4765_, v___y_4768_);
                crate::leanh::lean_dec_ref(v___y_4768_);
                crate::leanh::lean_inc_n(v___y_4758_, 7);
                crate::leanh::lean_inc_n(v___y_4760_, 26);
                v___x_4770_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4770_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4770_, 1, v___y_4758_);
                crate::leanh::lean_ctor_set(v___x_4770_, 2, v___x_4769_);
                v___x_4771_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_4772_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_4773_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_4762_, 8);
                v___x_4774_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___x_4771_, v___x_4772_, v___x_4773_);
                v___x_4775_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                v___x_4776_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4776_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4776_, 1, v___x_4775_);
                v___x_4777_ = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
                v___x_4778_ = l_Lean_Syntax_SepArray_ofElems(v___x_4777_, v___y_4766_);
                crate::leanh::lean_dec_ref(v___y_4766_);
                v___x_4779_ = l_Array_append___redArg(v___y_4765_, v___x_4778_);
                crate::leanh::lean_dec_ref(v___x_4778_);
                v___x_4780_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4780_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4780_, 1, v___y_4758_);
                crate::leanh::lean_ctor_set(v___x_4780_, 2, v___x_4779_);
                v___x_4781_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                v___x_4782_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4782_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4782_, 1, v___x_4781_);
                v___x_4783_ = l_Lean_Syntax_node3(
                    v___y_4760_,
                    v___x_4774_,
                    v___x_4776_,
                    v___x_4780_,
                    v___x_4782_,
                );
                v___x_4784_ = l_Lean_Syntax_node1(v___y_4760_, v___y_4758_, v___x_4783_);
                crate::leanh::lean_inc_ref(v___y_4759_);
                v___x_4785_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4785_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4785_, 1, v___y_4759_);
                v___x_4786_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5,
                );
                v___x_4787_ = l_Lean_Elab_Command_elabElabRulesAux___closed__6;
                crate::leanh::lean_inc_n(v___y_4761_, 2);
                crate::leanh::lean_inc_n(v___y_4767_, 2);
                v___x_4788_ = l_Lean_addMacroScope(v___y_4767_, v___x_4787_, v___y_4761_);
                v___x_4789_ = crate::leanh::lean_box(0);
                v___x_4790_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4790_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4790_, 1, v___x_4786_);
                crate::leanh::lean_ctor_set(v___x_4790_, 2, v___x_4788_);
                crate::leanh::lean_ctor_set(v___x_4790_, 3, v___x_4789_);
                v___x_4791_ = lean_mk_syntax_ident(v_k_4356_);
                v___x_4792_ =
                    l_Lean_Syntax_node2(v___y_4760_, v___y_4758_, v___x_4790_, v___x_4791_);
                v___x_4793_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_4794_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4794_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4794_, 1, v___x_4793_);
                v___x_4795_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__44),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__44_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__44,
                );
                v___x_4796_ = l_Lean_Elab_Command_elabElabRulesAux___closed__45;
                crate::leanh::lean_inc_ref_n(v___y_4764_, 2);
                v___x_4797_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___y_4764_, v___x_4796_, v___x_4796_);
                crate::leanh::lean_inc(v___x_4797_);
                v___x_4798_ = l_Lean_addMacroScope(v___y_4767_, v___x_4797_, v___y_4761_);
                v___x_4799_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4799_, 0, v___x_4797_);
                crate::leanh::lean_ctor_set(v___x_4799_, 1, v___x_4789_);
                v___x_4800_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4800_, 0, v___x_4799_);
                crate::leanh::lean_ctor_set(v___x_4800_, 1, v___x_4789_);
                v___x_4801_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4801_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4801_, 1, v___x_4795_);
                crate::leanh::lean_ctor_set(v___x_4801_, 2, v___x_4798_);
                crate::leanh::lean_ctor_set(v___x_4801_, 3, v___x_4800_);
                v___x_4802_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_4803_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4803_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4803_, 1, v___x_4802_);
                v___x_4804_ = l_Lean_Elab_Command_elabElabRulesAux___closed__12;
                v___x_4805_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___x_4771_, v___x_4772_, v___x_4804_);
                v___x_4806_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4806_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4806_, 1, v___x_4804_);
                v___x_4807_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                v___x_4808_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___x_4771_, v___x_4772_, v___x_4807_);
                v___x_4809_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_4810_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___x_4771_, v___x_4772_, v___x_4809_);
                v___x_4811_ = l_Array_append___redArg(v___y_4765_, v_a_4366_);
                crate::leanh::lean_dec(v_a_4366_);
                v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_4813_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4813_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4813_, 1, v___x_4812_);
                v___x_4814_ = l_Lean_Elab_Command_elabElabRulesAux___closed__17;
                v___x_4815_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___x_4771_, v___x_4772_, v___x_4814_);
                v___x_4816_ = l_Lean_Elab_Command_elabElabRulesAux___closed__18;
                v___x_4817_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4817_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4817_, 1, v___x_4816_);
                v___x_4818_ = l_Lean_Syntax_node1(v___y_4760_, v___x_4815_, v___x_4817_);
                v___x_4819_ = l_Lean_Syntax_node1(v___y_4760_, v___y_4758_, v___x_4818_);
                v___x_4820_ = l_Lean_Syntax_node1(v___y_4760_, v___y_4758_, v___x_4819_);
                v___x_4821_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_4822_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4822_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4822_, 1, v___x_4821_);
                v___x_4823_ = l_Lean_Elab_Command_elabElabRulesAux___closed__23;
                v___x_4824_ =
                    l_Lean_Name_mkStr4(v___y_4762_, v___x_4771_, v___x_4772_, v___x_4823_);
                v___x_4825_ = l_Lean_Elab_Command_elabElabRulesAux___closed__24;
                v___x_4826_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4826_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4826_, 1, v___x_4825_);
                v___x_4827_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
                v___x_4828_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26,
                );
                v___x_4829_ = l_Lean_Elab_Command_elabElabRulesAux___closed__27;
                v___x_4830_ = l_Lean_addMacroScope(v___y_4767_, v___x_4829_, v___y_4761_);
                v___x_4831_ = l_Lean_Name_mkStr3(v___y_4762_, v___y_4764_, v___x_4827_);
                v___x_4832_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4832_, 0, v___x_4831_);
                crate::leanh::lean_ctor_set(v___x_4832_, 1, v___x_4789_);
                v___x_4833_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4833_, 0, v___x_4832_);
                crate::leanh::lean_ctor_set(v___x_4833_, 1, v___x_4789_);
                v___x_4834_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4834_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4834_, 1, v___x_4828_);
                crate::leanh::lean_ctor_set(v___x_4834_, 2, v___x_4830_);
                crate::leanh::lean_ctor_set(v___x_4834_, 3, v___x_4833_);
                v___x_4835_ =
                    l_Lean_Syntax_node2(v___y_4760_, v___x_4824_, v___x_4826_, v___x_4834_);
                v___x_4836_ = l_Lean_Syntax_node4(
                    v___y_4760_,
                    v___x_4810_,
                    v___x_4813_,
                    v___x_4820_,
                    v___x_4822_,
                    v___x_4835_,
                );
                v___x_4837_ = lean_array_push(v___x_4811_, v___x_4836_);
                v___x_4838_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4838_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4838_, 1, v___y_4758_);
                crate::leanh::lean_ctor_set(v___x_4838_, 2, v___x_4837_);
                v___x_4839_ = l_Lean_Syntax_node1(v___y_4760_, v___x_4808_, v___x_4838_);
                v___x_4840_ =
                    l_Lean_Syntax_node2(v___y_4760_, v___x_4805_, v___x_4806_, v___x_4839_);
                v___x_4841_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_4842_ = lean_mk_empty_array_with_capacity(v___x_4841_);
                v___x_4843_ = lean_array_push(v___x_4842_, v___x_4770_);
                v___x_4844_ = lean_array_push(v___x_4843_, v___x_4784_);
                v___x_4845_ = lean_array_push(v___x_4844_, v___y_4763_);
                v___x_4846_ = lean_array_push(v___x_4845_, v___x_4785_);
                v___x_4847_ = lean_array_push(v___x_4846_, v___x_4792_);
                v___x_4848_ = lean_array_push(v___x_4847_, v___x_4794_);
                v___x_4849_ = lean_array_push(v___x_4848_, v___x_4801_);
                v___x_4850_ = lean_array_push(v___x_4849_, v___x_4803_);
                v___x_4851_ = lean_array_push(v___x_4850_, v___x_4840_);
                crate::leanh::lean_inc(v___y_4757_);
                v___x_4852_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4852_, 0, v___y_4760_);
                crate::leanh::lean_ctor_set(v___x_4852_, 1, v___y_4757_);
                crate::leanh::lean_ctor_set(v___x_4852_, 2, v___x_4851_);
                v___x_4853_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4853_, 0, v___x_4852_);
                return v___x_4853_;
            }
            10 => {
                v___x_4860_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_4861_ = l_Lean_Elab_Command_elabElabRulesAux___closed__28;
                v___x_4862_ = l_Lean_Elab_Command_elabElabRulesAux___closed__30;
                v___x_4863_ = l_Lean_Elab_Command_elabElabRulesAux___closed__31;
                v___x_4864_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_4865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_4353_) == 1 {
                    v_val_4866_ = crate::leanh::lean_ctor_get(v_doc_x3f_4353_, 0);
                    crate::leanh::lean_inc(v_val_4866_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_4353_, 1);
                    v___x_4867_ = l_Array_mkArray1___redArg(v_val_4866_);
                    v___y_4757_ = v___x_4863_;
                    v___y_4758_ = v___x_4864_;
                    v___y_4759_ = v___x_4862_;
                    v___y_4760_ = v___y_4855_;
                    v___y_4761_ = v___y_4856_;
                    v___y_4762_ = v___x_4860_;
                    v___y_4763_ = v___y_4857_;
                    v___y_4764_ = v___x_4861_;
                    v___y_4765_ = v___x_4865_;
                    v___y_4766_ = v___y_4858_;
                    v___y_4767_ = v_a_4859_;
                    v___y_4768_ = v___x_4867_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v___x_4868_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_4757_ = v___x_4863_;
                    v___y_4758_ = v___x_4864_;
                    v___y_4759_ = v___x_4862_;
                    v___y_4760_ = v___y_4855_;
                    v___y_4761_ = v___y_4856_;
                    v___y_4762_ = v___x_4860_;
                    v___y_4763_ = v___y_4857_;
                    v___y_4764_ = v___x_4861_;
                    v___y_4765_ = v___x_4865_;
                    v___y_4766_ = v___y_4858_;
                    v___y_4767_ = v_a_4859_;
                    v___y_4768_ = v___x_4868_;
                    state = 9;
                    continue;
                }
            }
            11 => {
                crate::leanh::lean_inc_ref_n(v___y_4875_, 4);
                v___x_4883_ = l_Array_append___redArg(v___y_4875_, v___y_4882_);
                crate::leanh::lean_dec_ref(v___y_4882_);
                crate::leanh::lean_inc_n(v___y_4878_, 12);
                crate::leanh::lean_inc_n(v___y_4877_, 42);
                v___x_4884_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4884_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4884_, 1, v___y_4878_);
                crate::leanh::lean_ctor_set(v___x_4884_, 2, v___x_4883_);
                v___x_4885_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_4886_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_4887_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_4871_, 13);
                v___x_4888_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4887_);
                v___x_4889_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                v___x_4890_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4890_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4890_, 1, v___x_4889_);
                v___x_4891_ = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
                v___x_4892_ = l_Lean_Syntax_SepArray_ofElems(v___x_4891_, v___y_4880_);
                crate::leanh::lean_dec_ref(v___y_4880_);
                v___x_4893_ = l_Array_append___redArg(v___y_4875_, v___x_4892_);
                crate::leanh::lean_dec_ref(v___x_4892_);
                v___x_4894_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4894_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4894_, 1, v___y_4878_);
                crate::leanh::lean_ctor_set(v___x_4894_, 2, v___x_4893_);
                v___x_4895_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                v___x_4896_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4896_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4896_, 1, v___x_4895_);
                v___x_4897_ = l_Lean_Syntax_node3(
                    v___y_4877_,
                    v___x_4888_,
                    v___x_4890_,
                    v___x_4894_,
                    v___x_4896_,
                );
                v___x_4898_ = l_Lean_Syntax_node1(v___y_4877_, v___y_4878_, v___x_4897_);
                crate::leanh::lean_inc_ref(v___y_4872_);
                v___x_4899_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4899_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4899_, 1, v___y_4872_);
                v___x_4900_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5,
                );
                v___x_4901_ = l_Lean_Elab_Command_elabElabRulesAux___closed__6;
                crate::leanh::lean_inc_n(v___y_4881_, 5);
                crate::leanh::lean_inc_n(v___y_4873_, 5);
                v___x_4902_ = l_Lean_addMacroScope(v___y_4873_, v___x_4901_, v___y_4881_);
                v___x_4903_ = crate::leanh::lean_box(0);
                v___x_4904_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4904_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4904_, 1, v___x_4900_);
                crate::leanh::lean_ctor_set(v___x_4904_, 2, v___x_4902_);
                crate::leanh::lean_ctor_set(v___x_4904_, 3, v___x_4903_);
                v___x_4905_ = lean_mk_syntax_ident(v_k_4356_);
                v___x_4906_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___y_4878_, v___x_4904_, v___x_4905_);
                v___x_4907_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_4908_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4908_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4908_, 1, v___x_4907_);
                v___x_4909_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__9_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__9,
                );
                v___x_4910_ = l_Lean_Elab_Command_elabElabRulesAux___closed__10;
                crate::leanh::lean_inc_ref_n(v___y_4874_, 3);
                v___x_4911_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___y_4874_, v___x_4886_, v___x_4910_);
                crate::leanh::lean_inc(v___x_4911_);
                v___x_4912_ = l_Lean_addMacroScope(v___y_4873_, v___x_4911_, v___y_4881_);
                v___x_4913_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4913_, 0, v___x_4911_);
                crate::leanh::lean_ctor_set(v___x_4913_, 1, v___x_4903_);
                v___x_4914_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4914_, 0, v___x_4913_);
                crate::leanh::lean_ctor_set(v___x_4914_, 1, v___x_4903_);
                v___x_4915_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4915_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4915_, 1, v___x_4909_);
                crate::leanh::lean_ctor_set(v___x_4915_, 2, v___x_4912_);
                crate::leanh::lean_ctor_set(v___x_4915_, 3, v___x_4914_);
                v___x_4916_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_4917_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4917_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4917_, 1, v___x_4916_);
                v___x_4918_ = l_Lean_Elab_Command_elabElabRulesAux___closed__12;
                v___x_4919_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4918_);
                v___x_4920_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4920_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4920_, 1, v___x_4918_);
                v___x_4921_ = l_Lean_Elab_Command_elabElabRulesAux___closed__13;
                v___x_4922_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4921_);
                v___x_4923_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15,
                );
                v___x_4924_ = l_Lean_Elab_Command_elabElabRulesAux___closed__16;
                v___x_4925_ = l_Lean_addMacroScope(v___y_4873_, v___x_4924_, v___y_4881_);
                v___x_4926_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4926_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4926_, 1, v___x_4923_);
                crate::leanh::lean_ctor_set(v___x_4926_, 2, v___x_4925_);
                crate::leanh::lean_ctor_set(v___x_4926_, 3, v___x_4903_);
                v___x_4927_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__47),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__47_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__47,
                );
                v___x_4928_ = l_Lean_Elab_Command_elabElabRulesAux___closed__48;
                v___x_4929_ = l_Lean_addMacroScope(v___y_4873_, v___x_4928_, v___y_4881_);
                v___x_4930_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4930_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4930_, 1, v___x_4927_);
                crate::leanh::lean_ctor_set(v___x_4930_, 2, v___x_4929_);
                crate::leanh::lean_ctor_set(v___x_4930_, 3, v___x_4903_);
                crate::leanh::lean_inc_ref(v___x_4930_);
                crate::leanh::lean_inc_ref(v___x_4926_);
                v___x_4931_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___y_4878_, v___x_4926_, v___x_4930_);
                v___x_4932_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4932_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4932_, 1, v___y_4878_);
                crate::leanh::lean_ctor_set(v___x_4932_, 2, v___y_4875_);
                v___x_4933_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_4934_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4934_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4934_, 1, v___x_4933_);
                v___x_4935_ = l_Lean_Elab_Command_elabElabRulesAux___closed__49;
                v___x_4936_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4935_);
                v___x_4937_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__51),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__51_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__51,
                );
                v___x_4938_ = l_Lean_Elab_Command_elabElabRulesAux___closed__52;
                v___x_4939_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___y_4874_, v___x_4886_, v___x_4938_);
                crate::leanh::lean_inc(v___x_4939_);
                v___x_4940_ = l_Lean_addMacroScope(v___y_4873_, v___x_4939_, v___y_4881_);
                v___x_4941_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4941_, 0, v___x_4939_);
                crate::leanh::lean_ctor_set(v___x_4941_, 1, v___x_4903_);
                v___x_4942_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4942_, 0, v___x_4941_);
                crate::leanh::lean_ctor_set(v___x_4942_, 1, v___x_4903_);
                v___x_4943_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4943_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4943_, 1, v___x_4937_);
                crate::leanh::lean_ctor_set(v___x_4943_, 2, v___x_4940_);
                crate::leanh::lean_ctor_set(v___x_4943_, 3, v___x_4942_);
                v___x_4944_ = l_Lean_Syntax_node1(v___y_4877_, v___y_4878_, v___y_4876_);
                v___x_4945_ = l_Lean_Elab_Command_elabElabRulesAux___closed__19;
                v___x_4946_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4945_);
                v___x_4947_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4947_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4947_, 1, v___x_4945_);
                v___x_4948_ = l_Lean_Elab_Command_elabElabRulesAux___closed__20;
                v___x_4949_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4948_);
                crate::leanh::lean_inc_ref_n(v___x_4932_, 4);
                v___x_4950_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___x_4949_, v___x_4932_, v___x_4926_);
                v___x_4951_ = l_Lean_Syntax_node1(v___y_4877_, v___y_4878_, v___x_4950_);
                v___x_4952_ = l_Lean_Elab_Command_elabElabRulesAux___closed__21;
                v___x_4953_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4953_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4953_, 1, v___x_4952_);
                v___x_4954_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                v___x_4955_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4954_);
                v___x_4956_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_4957_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4956_);
                v___x_4958_ = l_Array_append___redArg(v___y_4875_, v_a_4366_);
                crate::leanh::lean_dec(v_a_4366_);
                v___x_4959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_4960_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4960_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4960_, 1, v___x_4959_);
                v___x_4961_ = l_Lean_Elab_Command_elabElabRulesAux___closed__17;
                v___x_4962_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4961_);
                v___x_4963_ = l_Lean_Elab_Command_elabElabRulesAux___closed__18;
                v___x_4964_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4964_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4964_, 1, v___x_4963_);
                v___x_4965_ = l_Lean_Syntax_node1(v___y_4877_, v___x_4962_, v___x_4964_);
                v___x_4966_ = l_Lean_Syntax_node1(v___y_4877_, v___y_4878_, v___x_4965_);
                v___x_4967_ = l_Lean_Syntax_node1(v___y_4877_, v___y_4878_, v___x_4966_);
                v___x_4968_ = l_Lean_Elab_Command_elabElabRulesAux___closed__23;
                v___x_4969_ =
                    l_Lean_Name_mkStr4(v___y_4871_, v___x_4885_, v___x_4886_, v___x_4968_);
                v___x_4970_ = l_Lean_Elab_Command_elabElabRulesAux___closed__24;
                v___x_4971_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4971_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4971_, 1, v___x_4970_);
                v___x_4972_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
                v___x_4973_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26,
                );
                v___x_4974_ = l_Lean_Elab_Command_elabElabRulesAux___closed__27;
                v___x_4975_ = l_Lean_addMacroScope(v___y_4873_, v___x_4974_, v___y_4881_);
                v___x_4976_ = l_Lean_Name_mkStr3(v___y_4871_, v___y_4874_, v___x_4972_);
                v___x_4977_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4977_, 0, v___x_4976_);
                crate::leanh::lean_ctor_set(v___x_4977_, 1, v___x_4903_);
                v___x_4978_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4978_, 0, v___x_4977_);
                crate::leanh::lean_ctor_set(v___x_4978_, 1, v___x_4903_);
                v___x_4979_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4979_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4979_, 1, v___x_4973_);
                crate::leanh::lean_ctor_set(v___x_4979_, 2, v___x_4975_);
                crate::leanh::lean_ctor_set(v___x_4979_, 3, v___x_4978_);
                v___x_4980_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___x_4969_, v___x_4971_, v___x_4979_);
                crate::leanh::lean_inc_ref_n(v___x_4934_, 2);
                v___x_4981_ = l_Lean_Syntax_node4(
                    v___y_4877_,
                    v___x_4957_,
                    v___x_4960_,
                    v___x_4967_,
                    v___x_4934_,
                    v___x_4980_,
                );
                v___x_4982_ = lean_array_push(v___x_4958_, v___x_4981_);
                v___x_4983_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4983_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_4983_, 1, v___y_4878_);
                crate::leanh::lean_ctor_set(v___x_4983_, 2, v___x_4982_);
                v___x_4984_ = l_Lean_Syntax_node1(v___y_4877_, v___x_4955_, v___x_4983_);
                v___x_4985_ = l_Lean_Syntax_node6(
                    v___y_4877_,
                    v___x_4946_,
                    v___x_4947_,
                    v___x_4932_,
                    v___x_4932_,
                    v___x_4951_,
                    v___x_4953_,
                    v___x_4984_,
                );
                crate::leanh::lean_inc(v___x_4922_);
                v___x_4986_ = l_Lean_Syntax_node4(
                    v___y_4877_,
                    v___x_4922_,
                    v___x_4944_,
                    v___x_4932_,
                    v___x_4934_,
                    v___x_4985_,
                );
                crate::leanh::lean_inc_ref(v___x_4920_);
                crate::leanh::lean_inc(v___x_4919_);
                v___x_4987_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___x_4919_, v___x_4920_, v___x_4986_);
                v___x_4988_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___y_4878_, v___x_4930_, v___x_4987_);
                v___x_4989_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___x_4936_, v___x_4943_, v___x_4988_);
                v___x_4990_ = l_Lean_Syntax_node4(
                    v___y_4877_,
                    v___x_4922_,
                    v___x_4931_,
                    v___x_4932_,
                    v___x_4934_,
                    v___x_4989_,
                );
                v___x_4991_ =
                    l_Lean_Syntax_node2(v___y_4877_, v___x_4919_, v___x_4920_, v___x_4990_);
                v___x_4992_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_4993_ = lean_mk_empty_array_with_capacity(v___x_4992_);
                v___x_4994_ = lean_array_push(v___x_4993_, v___x_4884_);
                v___x_4995_ = lean_array_push(v___x_4994_, v___x_4898_);
                v___x_4996_ = lean_array_push(v___x_4995_, v___y_4879_);
                v___x_4997_ = lean_array_push(v___x_4996_, v___x_4899_);
                v___x_4998_ = lean_array_push(v___x_4997_, v___x_4906_);
                v___x_4999_ = lean_array_push(v___x_4998_, v___x_4908_);
                v___x_5000_ = lean_array_push(v___x_4999_, v___x_4915_);
                v___x_5001_ = lean_array_push(v___x_5000_, v___x_4917_);
                v___x_5002_ = lean_array_push(v___x_5001_, v___x_4991_);
                crate::leanh::lean_inc(v___y_4870_);
                v___x_5003_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5003_, 0, v___y_4877_);
                crate::leanh::lean_ctor_set(v___x_5003_, 1, v___y_4870_);
                crate::leanh::lean_ctor_set(v___x_5003_, 2, v___x_5002_);
                v___x_5004_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5004_, 0, v___x_5003_);
                return v___x_5004_;
            }
            12 => {
                v___x_5012_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_5013_ = l_Lean_Elab_Command_elabElabRulesAux___closed__28;
                v___x_5014_ = l_Lean_Elab_Command_elabElabRulesAux___closed__30;
                v___x_5015_ = l_Lean_Elab_Command_elabElabRulesAux___closed__31;
                v___x_5016_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_5017_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_4353_) == 1 {
                    v_val_5018_ = crate::leanh::lean_ctor_get(v_doc_x3f_4353_, 0);
                    crate::leanh::lean_inc(v_val_5018_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_4353_, 1);
                    v___x_5019_ = l_Array_mkArray1___redArg(v_val_5018_);
                    v___y_4870_ = v___x_5015_;
                    v___y_4871_ = v___x_5012_;
                    v___y_4872_ = v___x_5014_;
                    v___y_4873_ = v_a_5011_;
                    v___y_4874_ = v___x_5013_;
                    v___y_4875_ = v___x_5017_;
                    v___y_4876_ = v___y_5006_;
                    v___y_4877_ = v___y_5007_;
                    v___y_4878_ = v___x_5016_;
                    v___y_4879_ = v___y_5008_;
                    v___y_4880_ = v___y_5009_;
                    v___y_4881_ = v___y_5010_;
                    v___y_4882_ = v___x_5019_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v___x_5020_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_4870_ = v___x_5015_;
                    v___y_4871_ = v___x_5012_;
                    v___y_4872_ = v___x_5014_;
                    v___y_4873_ = v_a_5011_;
                    v___y_4874_ = v___x_5013_;
                    v___y_4875_ = v___x_5017_;
                    v___y_4876_ = v___y_5006_;
                    v___y_4877_ = v___y_5007_;
                    v___y_4878_ = v___x_5016_;
                    v___y_4879_ = v___y_5008_;
                    v___y_4880_ = v___y_5009_;
                    v___y_4881_ = v___y_5010_;
                    v___y_4882_ = v___x_5020_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc_ref_n(v___y_5022_, 4);
                v___x_5035_ = l_Array_append___redArg(v___y_5022_, v___y_5034_);
                crate::leanh::lean_dec_ref(v___y_5034_);
                crate::leanh::lean_inc_n(v___y_5027_, 10);
                crate::leanh::lean_inc_n(v___y_5025_, 35);
                v___x_5036_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5036_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5036_, 1, v___y_5027_);
                crate::leanh::lean_ctor_set(v___x_5036_, 2, v___x_5035_);
                v___x_5037_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_5038_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_5039_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                crate::leanh::lean_inc_ref_n(v___y_5031_, 11);
                v___x_5040_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5039_);
                v___x_5041_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                v___x_5042_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5042_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5042_, 1, v___x_5041_);
                v___x_5043_ = l_Lean_Elab_Command_elabElabRulesAux___closed__2;
                v___x_5044_ = l_Lean_Syntax_SepArray_ofElems(v___x_5043_, v___y_5032_);
                crate::leanh::lean_dec_ref(v___y_5032_);
                v___x_5045_ = l_Array_append___redArg(v___y_5022_, v___x_5044_);
                crate::leanh::lean_dec_ref(v___x_5044_);
                v___x_5046_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5046_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5046_, 1, v___y_5027_);
                crate::leanh::lean_ctor_set(v___x_5046_, 2, v___x_5045_);
                v___x_5047_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                v___x_5048_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5048_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5048_, 1, v___x_5047_);
                v___x_5049_ = l_Lean_Syntax_node3(
                    v___y_5025_,
                    v___x_5040_,
                    v___x_5042_,
                    v___x_5046_,
                    v___x_5048_,
                );
                v___x_5050_ = l_Lean_Syntax_node1(v___y_5025_, v___y_5027_, v___x_5049_);
                crate::leanh::lean_inc_ref(v___y_5030_);
                v___x_5051_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5051_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5051_, 1, v___y_5030_);
                v___x_5052_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__5_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__5,
                );
                v___x_5053_ = l_Lean_Elab_Command_elabElabRulesAux___closed__6;
                crate::leanh::lean_inc_n(v___y_5023_, 3);
                crate::leanh::lean_inc_n(v___y_5026_, 3);
                v___x_5054_ = l_Lean_addMacroScope(v___y_5026_, v___x_5053_, v___y_5023_);
                v___x_5055_ = crate::leanh::lean_box(0);
                v___x_5056_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5056_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5056_, 1, v___x_5052_);
                crate::leanh::lean_ctor_set(v___x_5056_, 2, v___x_5054_);
                crate::leanh::lean_ctor_set(v___x_5056_, 3, v___x_5055_);
                v___x_5057_ = lean_mk_syntax_ident(v_k_4356_);
                v___x_5058_ =
                    l_Lean_Syntax_node2(v___y_5025_, v___y_5027_, v___x_5056_, v___x_5057_);
                v___x_5059_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_5060_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5060_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5060_, 1, v___x_5059_);
                v___x_5061_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__37),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__37_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__37,
                );
                v___x_5062_ = l_Lean_Elab_Command_elabElabRulesAux___closed__38;
                v___x_5063_ = l_Lean_Elab_Command_elabElabRulesAux___closed__39;
                crate::leanh::lean_inc_ref_n(v___y_5024_, 2);
                v___x_5064_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___y_5024_, v___x_5062_, v___x_5063_);
                crate::leanh::lean_inc(v___x_5064_);
                v___x_5065_ = l_Lean_addMacroScope(v___y_5026_, v___x_5064_, v___y_5023_);
                v___x_5066_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5066_, 0, v___x_5064_);
                crate::leanh::lean_ctor_set(v___x_5066_, 1, v___x_5055_);
                v___x_5067_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5067_, 0, v___x_5066_);
                crate::leanh::lean_ctor_set(v___x_5067_, 1, v___x_5055_);
                v___x_5068_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5068_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5068_, 1, v___x_5061_);
                crate::leanh::lean_ctor_set(v___x_5068_, 2, v___x_5065_);
                crate::leanh::lean_ctor_set(v___x_5068_, 3, v___x_5067_);
                v___x_5069_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_5070_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5070_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5070_, 1, v___x_5069_);
                v___x_5071_ = l_Lean_Elab_Command_elabElabRulesAux___closed__12;
                v___x_5072_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5071_);
                v___x_5073_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5073_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5073_, 1, v___x_5071_);
                v___x_5074_ = l_Lean_Elab_Command_elabElabRulesAux___closed__13;
                v___x_5075_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5074_);
                v___x_5076_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__15_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__15,
                );
                v___x_5077_ = l_Lean_Elab_Command_elabElabRulesAux___closed__16;
                v___x_5078_ = l_Lean_addMacroScope(v___y_5026_, v___x_5077_, v___y_5023_);
                v___x_5079_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5079_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5079_, 1, v___x_5076_);
                crate::leanh::lean_ctor_set(v___x_5079_, 2, v___x_5078_);
                crate::leanh::lean_ctor_set(v___x_5079_, 3, v___x_5055_);
                crate::leanh::lean_inc_ref(v___x_5079_);
                v___x_5080_ =
                    l_Lean_Syntax_node2(v___y_5025_, v___y_5027_, v___x_5079_, v___y_5028_);
                v___x_5081_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5081_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5081_, 1, v___y_5027_);
                crate::leanh::lean_ctor_set(v___x_5081_, 2, v___y_5022_);
                v___x_5082_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_5083_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5083_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5083_, 1, v___x_5082_);
                v___x_5084_ = l_Lean_Elab_Command_elabElabRulesAux___closed__19;
                v___x_5085_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5084_);
                v___x_5086_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5086_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5086_, 1, v___x_5084_);
                v___x_5087_ = l_Lean_Elab_Command_elabElabRulesAux___closed__20;
                v___x_5088_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5087_);
                crate::leanh::lean_inc_ref_n(v___x_5081_, 3);
                v___x_5089_ =
                    l_Lean_Syntax_node2(v___y_5025_, v___x_5088_, v___x_5081_, v___x_5079_);
                v___x_5090_ = l_Lean_Syntax_node1(v___y_5025_, v___y_5027_, v___x_5089_);
                v___x_5091_ = l_Lean_Elab_Command_elabElabRulesAux___closed__21;
                v___x_5092_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5092_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5092_, 1, v___x_5091_);
                v___x_5093_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                v___x_5094_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5093_);
                v___x_5095_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_5096_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5095_);
                v___x_5097_ = l_Array_append___redArg(v___y_5022_, v_a_4366_);
                crate::leanh::lean_dec(v_a_4366_);
                v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_5099_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5099_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5099_, 1, v___x_5098_);
                v___x_5100_ = l_Lean_Elab_Command_elabElabRulesAux___closed__17;
                v___x_5101_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5100_);
                v___x_5102_ = l_Lean_Elab_Command_elabElabRulesAux___closed__18;
                v___x_5103_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5103_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5103_, 1, v___x_5102_);
                v___x_5104_ = l_Lean_Syntax_node1(v___y_5025_, v___x_5101_, v___x_5103_);
                v___x_5105_ = l_Lean_Syntax_node1(v___y_5025_, v___y_5027_, v___x_5104_);
                v___x_5106_ = l_Lean_Syntax_node1(v___y_5025_, v___y_5027_, v___x_5105_);
                v___x_5107_ = l_Lean_Elab_Command_elabElabRulesAux___closed__23;
                v___x_5108_ =
                    l_Lean_Name_mkStr4(v___y_5031_, v___x_5037_, v___x_5038_, v___x_5107_);
                v___x_5109_ = l_Lean_Elab_Command_elabElabRulesAux___closed__24;
                v___x_5110_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5110_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5110_, 1, v___x_5109_);
                v___x_5111_ = l_Lean_Elab_Command_elabElabRulesAux___closed__25;
                v___x_5112_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__26_once),
                    _init_l_Lean_Elab_Command_elabElabRulesAux___closed__26,
                );
                v___x_5113_ = l_Lean_Elab_Command_elabElabRulesAux___closed__27;
                v___x_5114_ = l_Lean_addMacroScope(v___y_5026_, v___x_5113_, v___y_5023_);
                v___x_5115_ = l_Lean_Name_mkStr3(v___y_5031_, v___y_5024_, v___x_5111_);
                v___x_5116_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5116_, 0, v___x_5115_);
                crate::leanh::lean_ctor_set(v___x_5116_, 1, v___x_5055_);
                v___x_5117_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5117_, 0, v___x_5116_);
                crate::leanh::lean_ctor_set(v___x_5117_, 1, v___x_5055_);
                v___x_5118_ = crate::leanh::lean_alloc_ctor(3, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5118_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5118_, 1, v___x_5112_);
                crate::leanh::lean_ctor_set(v___x_5118_, 2, v___x_5114_);
                crate::leanh::lean_ctor_set(v___x_5118_, 3, v___x_5117_);
                v___x_5119_ =
                    l_Lean_Syntax_node2(v___y_5025_, v___x_5108_, v___x_5110_, v___x_5118_);
                crate::leanh::lean_inc_ref(v___x_5083_);
                v___x_5120_ = l_Lean_Syntax_node4(
                    v___y_5025_,
                    v___x_5096_,
                    v___x_5099_,
                    v___x_5106_,
                    v___x_5083_,
                    v___x_5119_,
                );
                v___x_5121_ = lean_array_push(v___x_5097_, v___x_5120_);
                v___x_5122_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5122_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5122_, 1, v___y_5027_);
                crate::leanh::lean_ctor_set(v___x_5122_, 2, v___x_5121_);
                v___x_5123_ = l_Lean_Syntax_node1(v___y_5025_, v___x_5094_, v___x_5122_);
                v___x_5124_ = l_Lean_Syntax_node6(
                    v___y_5025_,
                    v___x_5085_,
                    v___x_5086_,
                    v___x_5081_,
                    v___x_5081_,
                    v___x_5090_,
                    v___x_5092_,
                    v___x_5123_,
                );
                v___x_5125_ = l_Lean_Syntax_node4(
                    v___y_5025_,
                    v___x_5075_,
                    v___x_5080_,
                    v___x_5081_,
                    v___x_5083_,
                    v___x_5124_,
                );
                v___x_5126_ =
                    l_Lean_Syntax_node2(v___y_5025_, v___x_5072_, v___x_5073_, v___x_5125_);
                v___x_5127_ = crate::leanh::lean_unsigned_to_nat(9);
                v___x_5128_ = lean_mk_empty_array_with_capacity(v___x_5127_);
                v___x_5129_ = lean_array_push(v___x_5128_, v___x_5036_);
                v___x_5130_ = lean_array_push(v___x_5129_, v___x_5050_);
                v___x_5131_ = lean_array_push(v___x_5130_, v___y_5033_);
                v___x_5132_ = lean_array_push(v___x_5131_, v___x_5051_);
                v___x_5133_ = lean_array_push(v___x_5132_, v___x_5058_);
                v___x_5134_ = lean_array_push(v___x_5133_, v___x_5060_);
                v___x_5135_ = lean_array_push(v___x_5134_, v___x_5068_);
                v___x_5136_ = lean_array_push(v___x_5135_, v___x_5070_);
                v___x_5137_ = lean_array_push(v___x_5136_, v___x_5126_);
                crate::leanh::lean_inc(v___y_5029_);
                v___x_5138_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5138_, 0, v___y_5025_);
                crate::leanh::lean_ctor_set(v___x_5138_, 1, v___y_5029_);
                crate::leanh::lean_ctor_set(v___x_5138_, 2, v___x_5137_);
                v___x_5139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5139_, 0, v___x_5138_);
                return v___x_5139_;
            }
            14 => {
                v___x_5147_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_5148_ = l_Lean_Elab_Command_elabElabRulesAux___closed__28;
                v___x_5149_ = l_Lean_Elab_Command_elabElabRulesAux___closed__30;
                v___x_5150_ = l_Lean_Elab_Command_elabElabRulesAux___closed__31;
                v___x_5151_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_5152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_4353_) == 1 {
                    v_val_5153_ = crate::leanh::lean_ctor_get(v_doc_x3f_4353_, 0);
                    crate::leanh::lean_inc(v_val_5153_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_4353_, 1);
                    v___x_5154_ = l_Array_mkArray1___redArg(v_val_5153_);
                    v___y_5022_ = v___x_5152_;
                    v___y_5023_ = v___y_5144_;
                    v___y_5024_ = v___x_5148_;
                    v___y_5025_ = v___y_5145_;
                    v___y_5026_ = v_a_5146_;
                    v___y_5027_ = v___x_5151_;
                    v___y_5028_ = v___y_5141_;
                    v___y_5029_ = v___x_5150_;
                    v___y_5030_ = v___x_5149_;
                    v___y_5031_ = v___x_5147_;
                    v___y_5032_ = v___y_5143_;
                    v___y_5033_ = v___y_5142_;
                    v___y_5034_ = v___x_5154_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v___x_5155_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_5022_ = v___x_5152_;
                    v___y_5023_ = v___y_5144_;
                    v___y_5024_ = v___x_5148_;
                    v___y_5025_ = v___y_5145_;
                    v___y_5026_ = v_a_5146_;
                    v___y_5027_ = v___x_5151_;
                    v___y_5028_ = v___y_5141_;
                    v___y_5029_ = v___x_5150_;
                    v___y_5030_ = v___x_5149_;
                    v___y_5031_ = v___x_5147_;
                    v___y_5032_ = v___y_5143_;
                    v___y_5033_ = v___y_5142_;
                    v___y_5034_ = v___x_5155_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v___y_5158_);
                crate::leanh::lean_inc(v_k_4356_);
                v___x_5162_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
                    v_k_4356_,
                    v_attrKind_4355_,
                    v_attrs_x3f_4354_,
                    v___y_5158_,
                    v___y_5161_,
                    v___y_5160_,
                );
                if crate::leanh::lean_obj_tag(v___x_5162_) == 0 {
                    v_a_5163_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
                    crate::leanh::lean_inc(v_a_5163_);
                    crate::leanh::lean_dec_ref_known(v___x_5162_, 1);
                    v___x_5164_ = l_Lean_Elab_Command_getRef___redArg(v___y_5161_);
                    if crate::leanh::lean_obj_tag(v___x_5164_) == 0 {
                        v_a_5165_ = crate::leanh::lean_ctor_get(v___x_5164_, 0);
                        crate::leanh::lean_inc(v_a_5165_);
                        crate::leanh::lean_dec_ref_known(v___x_5164_, 1);
                        v___x_5166_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5161_);
                        if crate::leanh::lean_obj_tag(v___x_5166_) == 0 {
                            v_a_5167_ = crate::leanh::lean_ctor_get(v___x_5166_, 0);
                            crate::leanh::lean_inc(v_a_5167_);
                            crate::leanh::lean_dec_ref_known(v___x_5166_, 1);
                            v_quotContext_x3f_5168_ = crate::leanh::lean_ctor_get(v___y_5161_, 5);
                            v___x_5169_ = l_Lean_SourceInfo_fromRef(v_a_5165_, v___y_5157_);
                            crate::leanh::lean_dec(v_a_5165_);
                            if crate::leanh::lean_obj_tag(v_quotContext_x3f_5168_) == 0 {
                                v___x_5170_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5160_);
                                v_a_5171_ = crate::leanh::lean_ctor_get(v___x_5170_, 0);
                                crate::leanh::lean_inc(v_a_5171_);
                                crate::leanh::lean_dec_ref(v___x_5170_);
                                v___y_4855_ = v___x_5169_;
                                v___y_4856_ = v_a_5167_;
                                v___y_4857_ = v___y_5159_;
                                v___y_4858_ = v_a_5163_;
                                v_a_4859_ = v_a_5171_;
                                state = 10;
                                continue;
                            } else {
                                v_val_5172_ =
                                    crate::leanh::lean_ctor_get(v_quotContext_x3f_5168_, 0);
                                crate::leanh::lean_inc(v_val_5172_);
                                v___y_4855_ = v___x_5169_;
                                v___y_4856_ = v_a_5167_;
                                v___y_4857_ = v___y_5159_;
                                v___y_4858_ = v_a_5163_;
                                v_a_4859_ = v_val_5172_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5165_);
                            crate::leanh::lean_dec(v_a_5163_);
                            crate::leanh::lean_dec(v___y_5159_);
                            crate::leanh::lean_dec(v_a_4366_);
                            crate::leanh::lean_dec(v_k_4356_);
                            crate::leanh::lean_dec(v_doc_x3f_4353_);
                            v_a_5173_ = crate::leanh::lean_ctor_get(v___x_5166_, 0);
                            v_isSharedCheck_5180_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5166_)) as u8;
                            if v_isSharedCheck_5180_ == 0 {
                                v___x_5175_ = v___x_5166_;
                                v_isShared_5176_ = v_isSharedCheck_5180_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5173_);
                                crate::leanh::lean_dec(v___x_5166_);
                                v___x_5175_ = crate::leanh::lean_box(0);
                                v_isShared_5176_ = v_isSharedCheck_5180_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5163_);
                        crate::leanh::lean_dec(v___y_5159_);
                        crate::leanh::lean_dec(v_a_4366_);
                        crate::leanh::lean_dec(v_k_4356_);
                        crate::leanh::lean_dec(v_doc_x3f_4353_);
                        return v___x_5164_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5159_);
                    crate::leanh::lean_dec(v_a_4366_);
                    crate::leanh::lean_dec(v_k_4356_);
                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                    v_a_5181_ = crate::leanh::lean_ctor_get(v___x_5162_, 0);
                    v_isSharedCheck_5188_ = (!crate::leanh::lean_is_exclusive(v___x_5162_)) as u8;
                    if v_isSharedCheck_5188_ == 0 {
                        v___x_5183_ = v___x_5162_;
                        v_isShared_5184_ = v_isSharedCheck_5188_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5181_);
                        crate::leanh::lean_dec(v___x_5162_);
                        v___x_5183_ = crate::leanh::lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5188_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_5176_ == 0 {
                    v___x_5178_ = v___x_5175_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5179_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5179_, 0, v_a_5173_);
                    v___x_5178_ = v_reuseFailAlloc_5179_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_5178_;
            }
            18 => {
                if v_isShared_5184_ == 0 {
                    v___x_5186_ = v___x_5183_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_5187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_a_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5187_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_5186_;
            }
            20 => {
                crate::leanh::lean_inc(v_attrKind_4355_);
                v___x_5193_ = l_Lean_Parser_Command_visibility_ofAttrKind(v_attrKind_4355_);
                if crate::leanh::lean_obj_tag(v_expty_x3f_4358_) == 1 {
                    crate::leanh::lean_del_object(v___x_4368_);
                    v_val_5194_ = crate::leanh::lean_ctor_get(v_expty_x3f_4358_, 0);
                    crate::leanh::lean_inc(v_val_5194_);
                    crate::leanh::lean_dec_ref_known(v_expty_x3f_4358_, 1);
                    v___x_5195_ = l_Lean_Elab_Command_elabElabRulesAux___closed__54;
                    v___x_5196_ = lean_name_eq(v_catName_5190_, v___x_5195_);
                    if v___x_5196_ == 0 {
                        v___x_5197_ = l_Lean_Elab_Command_elabElabRulesAux___closed__56;
                        v___x_5198_ = lean_name_eq(v_catName_5190_, v___x_5197_);
                        if v___x_5198_ == 0 {
                            crate::leanh::lean_dec(v___x_5193_);
                            crate::leanh::lean_dec(v_a_4366_);
                            crate::leanh::lean_dec(v_k_4356_);
                            crate::leanh::lean_dec(v_attrKind_4355_);
                            crate::leanh::lean_dec(v_doc_x3f_4353_);
                            v___x_5199_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabElabRulesAux___closed__58
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabElabRulesAux___closed__58_once
                                ),
                                _init_l_Lean_Elab_Command_elabElabRulesAux___closed__58,
                            );
                            v___x_5200_ = l_Lean_MessageData_ofName(v_catName_5190_);
                            v___x_5201_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5201_, 0, v___x_5199_);
                            crate::leanh::lean_ctor_set(v___x_5201_, 1, v___x_5200_);
                            v___x_5202_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabElabRulesAux___closed__60
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Command_elabElabRulesAux___closed__60_once
                                ),
                                _init_l_Lean_Elab_Command_elabElabRulesAux___closed__60,
                            );
                            v___x_5203_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5203_, 0, v___x_5201_);
                            crate::leanh::lean_ctor_set(v___x_5203_, 1, v___x_5202_);
                            v___x_5204_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_val_5194_, v___x_5203_, v___y_5191_, v___y_5192_);
                            crate::leanh::lean_dec(v_val_5194_);
                            return v___x_5204_;
                        } else {
                            crate::leanh::lean_dec(v_catName_5190_);
                            v___x_5205_ = l_Lean_Elab_Command_elabElabRulesAux___closed__62;
                            crate::leanh::lean_inc(v_k_4356_);
                            v___x_5206_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
                                v_k_4356_,
                                v_attrKind_4355_,
                                v_attrs_x3f_4354_,
                                v___x_5205_,
                                v___y_5191_,
                                v___y_5192_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5206_) == 0 {
                                v_a_5207_ = crate::leanh::lean_ctor_get(v___x_5206_, 0);
                                crate::leanh::lean_inc(v_a_5207_);
                                crate::leanh::lean_dec_ref_known(v___x_5206_, 1);
                                v___x_5208_ = l_Lean_Elab_Command_getRef___redArg(v___y_5191_);
                                if crate::leanh::lean_obj_tag(v___x_5208_) == 0 {
                                    v_a_5209_ = crate::leanh::lean_ctor_get(v___x_5208_, 0);
                                    crate::leanh::lean_inc(v_a_5209_);
                                    crate::leanh::lean_dec_ref_known(v___x_5208_, 1);
                                    v___x_5210_ =
                                        l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5191_);
                                    if crate::leanh::lean_obj_tag(v___x_5210_) == 0 {
                                        v_a_5211_ = crate::leanh::lean_ctor_get(v___x_5210_, 0);
                                        crate::leanh::lean_inc(v_a_5211_);
                                        crate::leanh::lean_dec_ref_known(v___x_5210_, 1);
                                        v_quotContext_x3f_5212_ =
                                            crate::leanh::lean_ctor_get(v___y_5191_, 5);
                                        v___x_5213_ =
                                            l_Lean_SourceInfo_fromRef(v_a_5209_, v___x_5196_);
                                        crate::leanh::lean_dec(v_a_5209_);
                                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_5212_) == 0
                                        {
                                            v___x_5214_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5192_);
                                            v_a_5215_ = crate::leanh::lean_ctor_get(v___x_5214_, 0);
                                            crate::leanh::lean_inc(v_a_5215_);
                                            crate::leanh::lean_dec_ref(v___x_5214_);
                                            v___y_5141_ = v_val_5194_;
                                            v___y_5142_ = v___x_5193_;
                                            v___y_5143_ = v_a_5207_;
                                            v___y_5144_ = v_a_5211_;
                                            v___y_5145_ = v___x_5213_;
                                            v_a_5146_ = v_a_5215_;
                                            state = 14;
                                            continue;
                                        } else {
                                            v_val_5216_ = crate::leanh::lean_ctor_get(
                                                v_quotContext_x3f_5212_,
                                                0,
                                            );
                                            crate::leanh::lean_inc(v_val_5216_);
                                            v___y_5141_ = v_val_5194_;
                                            v___y_5142_ = v___x_5193_;
                                            v___y_5143_ = v_a_5207_;
                                            v___y_5144_ = v_a_5211_;
                                            v___y_5145_ = v___x_5213_;
                                            v_a_5146_ = v_val_5216_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5209_);
                                        crate::leanh::lean_dec(v_a_5207_);
                                        crate::leanh::lean_dec(v_val_5194_);
                                        crate::leanh::lean_dec(v___x_5193_);
                                        crate::leanh::lean_dec(v_a_4366_);
                                        crate::leanh::lean_dec(v_k_4356_);
                                        crate::leanh::lean_dec(v_doc_x3f_4353_);
                                        v_a_5217_ = crate::leanh::lean_ctor_get(v___x_5210_, 0);
                                        v_isSharedCheck_5224_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5210_)) as u8;
                                        if v_isSharedCheck_5224_ == 0 {
                                            v___x_5219_ = v___x_5210_;
                                            v_isShared_5220_ = v_isSharedCheck_5224_;
                                            state = 21;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5217_);
                                            crate::leanh::lean_dec(v___x_5210_);
                                            v___x_5219_ = crate::leanh::lean_box(0);
                                            v_isShared_5220_ = v_isSharedCheck_5224_;
                                            state = 21;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5207_);
                                    crate::leanh::lean_dec(v_val_5194_);
                                    crate::leanh::lean_dec(v___x_5193_);
                                    crate::leanh::lean_dec(v_a_4366_);
                                    crate::leanh::lean_dec(v_k_4356_);
                                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                                    return v___x_5208_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_5194_);
                                crate::leanh::lean_dec(v___x_5193_);
                                crate::leanh::lean_dec(v_a_4366_);
                                crate::leanh::lean_dec(v_k_4356_);
                                crate::leanh::lean_dec(v_doc_x3f_4353_);
                                v_a_5225_ = crate::leanh::lean_ctor_get(v___x_5206_, 0);
                                v_isSharedCheck_5232_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5206_)) as u8;
                                if v_isSharedCheck_5232_ == 0 {
                                    v___x_5227_ = v___x_5206_;
                                    v_isShared_5228_ = v_isSharedCheck_5232_;
                                    state = 23;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5225_);
                                    crate::leanh::lean_dec(v___x_5206_);
                                    v___x_5227_ = crate::leanh::lean_box(0);
                                    v_isShared_5228_ = v_isSharedCheck_5232_;
                                    state = 23;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_catName_5190_);
                        v___x_5233_ = l_Lean_Elab_Command_elabElabRulesAux___closed__64;
                        crate::leanh::lean_inc(v_k_4356_);
                        v___x_5234_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
                            v_k_4356_,
                            v_attrKind_4355_,
                            v_attrs_x3f_4354_,
                            v___x_5233_,
                            v___y_5191_,
                            v___y_5192_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5234_) == 0 {
                            v_a_5235_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                            crate::leanh::lean_inc(v_a_5235_);
                            crate::leanh::lean_dec_ref_known(v___x_5234_, 1);
                            v___x_5236_ = l_Lean_Elab_Command_getRef___redArg(v___y_5191_);
                            if crate::leanh::lean_obj_tag(v___x_5236_) == 0 {
                                v_a_5237_ = crate::leanh::lean_ctor_get(v___x_5236_, 0);
                                crate::leanh::lean_inc(v_a_5237_);
                                crate::leanh::lean_dec_ref_known(v___x_5236_, 1);
                                v___x_5238_ =
                                    l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5191_);
                                if crate::leanh::lean_obj_tag(v___x_5238_) == 0 {
                                    v_a_5239_ = crate::leanh::lean_ctor_get(v___x_5238_, 0);
                                    crate::leanh::lean_inc(v_a_5239_);
                                    crate::leanh::lean_dec_ref_known(v___x_5238_, 1);
                                    v_quotContext_x3f_5240_ =
                                        crate::leanh::lean_ctor_get(v___y_5191_, 5);
                                    v___x_5241_ = 0;
                                    v___x_5242_ = l_Lean_SourceInfo_fromRef(v_a_5237_, v___x_5241_);
                                    crate::leanh::lean_dec(v_a_5237_);
                                    if crate::leanh::lean_obj_tag(v_quotContext_x3f_5240_) == 0 {
                                        v___x_5243_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5192_);
                                        v_a_5244_ = crate::leanh::lean_ctor_get(v___x_5243_, 0);
                                        crate::leanh::lean_inc(v_a_5244_);
                                        crate::leanh::lean_dec_ref(v___x_5243_);
                                        v___y_5006_ = v_val_5194_;
                                        v___y_5007_ = v___x_5242_;
                                        v___y_5008_ = v___x_5193_;
                                        v___y_5009_ = v_a_5235_;
                                        v___y_5010_ = v_a_5239_;
                                        v_a_5011_ = v_a_5244_;
                                        state = 12;
                                        continue;
                                    } else {
                                        v_val_5245_ =
                                            crate::leanh::lean_ctor_get(v_quotContext_x3f_5240_, 0);
                                        crate::leanh::lean_inc(v_val_5245_);
                                        v___y_5006_ = v_val_5194_;
                                        v___y_5007_ = v___x_5242_;
                                        v___y_5008_ = v___x_5193_;
                                        v___y_5009_ = v_a_5235_;
                                        v___y_5010_ = v_a_5239_;
                                        v_a_5011_ = v_val_5245_;
                                        state = 12;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5237_);
                                    crate::leanh::lean_dec(v_a_5235_);
                                    crate::leanh::lean_dec(v_val_5194_);
                                    crate::leanh::lean_dec(v___x_5193_);
                                    crate::leanh::lean_dec(v_a_4366_);
                                    crate::leanh::lean_dec(v_k_4356_);
                                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                                    v_a_5246_ = crate::leanh::lean_ctor_get(v___x_5238_, 0);
                                    v_isSharedCheck_5253_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5238_)) as u8;
                                    if v_isSharedCheck_5253_ == 0 {
                                        v___x_5248_ = v___x_5238_;
                                        v_isShared_5249_ = v_isSharedCheck_5253_;
                                        state = 25;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5246_);
                                        crate::leanh::lean_dec(v___x_5238_);
                                        v___x_5248_ = crate::leanh::lean_box(0);
                                        v_isShared_5249_ = v_isSharedCheck_5253_;
                                        state = 25;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5235_);
                                crate::leanh::lean_dec(v_val_5194_);
                                crate::leanh::lean_dec(v___x_5193_);
                                crate::leanh::lean_dec(v_a_4366_);
                                crate::leanh::lean_dec(v_k_4356_);
                                crate::leanh::lean_dec(v_doc_x3f_4353_);
                                return v___x_5236_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_5194_);
                            crate::leanh::lean_dec(v___x_5193_);
                            crate::leanh::lean_dec(v_a_4366_);
                            crate::leanh::lean_dec(v_k_4356_);
                            crate::leanh::lean_dec(v_doc_x3f_4353_);
                            v_a_5254_ = crate::leanh::lean_ctor_get(v___x_5234_, 0);
                            v_isSharedCheck_5261_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5234_)) as u8;
                            if v_isSharedCheck_5261_ == 0 {
                                v___x_5256_ = v___x_5234_;
                                v_isShared_5257_ = v_isSharedCheck_5261_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5254_);
                                crate::leanh::lean_dec(v___x_5234_);
                                v___x_5256_ = crate::leanh::lean_box(0);
                                v_isShared_5257_ = v_isSharedCheck_5261_;
                                state = 27;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_expty_x3f_4358_);
                    v___x_5262_ = l_Lean_Elab_Command_elabElabRulesAux___closed__54;
                    v___x_5263_ = lean_name_eq(v_catName_5190_, v___x_5262_);
                    if v___x_5263_ == 0 {
                        crate::leanh::lean_del_object(v___x_4368_);
                        v___x_5264_ = l_Lean_Elab_Command_elabElabRulesAux___closed__66;
                        v___x_5265_ = lean_name_eq(v_catName_5190_, v___x_5264_);
                        if v___x_5265_ == 0 {
                            v___x_5266_ = l_Lean_Elab_Command_elabElabRulesAux___closed__68;
                            v___x_5267_ = lean_name_eq(v_catName_5190_, v___x_5266_);
                            if v___x_5267_ == 0 {
                                v___x_5268_ = l_Lean_Elab_Command_elabElabRulesAux___closed__70;
                                v___x_5269_ = lean_name_eq(v_catName_5190_, v___x_5268_);
                                if v___x_5269_ == 0 {
                                    v___x_5270_ = l_Lean_Elab_Command_elabElabRulesAux___closed__56;
                                    v___x_5271_ = lean_name_eq(v_catName_5190_, v___x_5270_);
                                    if v___x_5271_ == 0 {
                                        crate::leanh::lean_dec(v___x_5193_);
                                        crate::leanh::lean_dec(v_a_4366_);
                                        crate::leanh::lean_dec(v_k_4356_);
                                        crate::leanh::lean_dec(v_attrKind_4355_);
                                        crate::leanh::lean_dec(v_doc_x3f_4353_);
                                        v___x_5272_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__72), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabElabRulesAux___closed__72_once), _init_l_Lean_Elab_Command_elabElabRulesAux___closed__72);
                                        v___x_5273_ = l_Lean_MessageData_ofName(v_catName_5190_);
                                        v___x_5274_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_5274_, 0, v___x_5272_);
                                        crate::leanh::lean_ctor_set(v___x_5274_, 1, v___x_5273_);
                                        v___x_5275_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__3);
                                        v___x_5276_ =
                                            crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                        crate::leanh::lean_ctor_set(v___x_5276_, 0, v___x_5274_);
                                        crate::leanh::lean_ctor_set(v___x_5276_, 1, v___x_5275_);
                                        v___x_5277_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(v___x_5276_, v___y_5191_, v___y_5192_);
                                        return v___x_5277_;
                                    } else {
                                        crate::leanh::lean_dec(v_catName_5190_);
                                        v___x_5278_ =
                                            l_Lean_Elab_Command_elabElabRulesAux___closed__62;
                                        crate::leanh::lean_inc(v_k_4356_);
                                        v___x_5279_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
                                            v_k_4356_,
                                            v_attrKind_4355_,
                                            v_attrs_x3f_4354_,
                                            v___x_5278_,
                                            v___y_5191_,
                                            v___y_5192_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5279_) == 0 {
                                            v_a_5280_ = crate::leanh::lean_ctor_get(v___x_5279_, 0);
                                            crate::leanh::lean_inc(v_a_5280_);
                                            crate::leanh::lean_dec_ref_known(v___x_5279_, 1);
                                            v___x_5281_ =
                                                l_Lean_Elab_Command_getRef___redArg(v___y_5191_);
                                            if crate::leanh::lean_obj_tag(v___x_5281_) == 0 {
                                                v_a_5282_ =
                                                    crate::leanh::lean_ctor_get(v___x_5281_, 0);
                                                crate::leanh::lean_inc(v_a_5282_);
                                                crate::leanh::lean_dec_ref_known(v___x_5281_, 1);
                                                v___x_5283_ =
                                                    l_Lean_Elab_Command_getCurrMacroScope___redArg(
                                                        v___y_5191_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_5283_) == 0 {
                                                    v_a_5284_ =
                                                        crate::leanh::lean_ctor_get(v___x_5283_, 0);
                                                    crate::leanh::lean_inc(v_a_5284_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_5283_,
                                                        1,
                                                    );
                                                    v_quotContext_x3f_5285_ =
                                                        crate::leanh::lean_ctor_get(v___y_5191_, 5);
                                                    v___x_5286_ = l_Lean_SourceInfo_fromRef(
                                                        v_a_5282_,
                                                        v___x_5269_,
                                                    );
                                                    crate::leanh::lean_dec(v_a_5282_);
                                                    if crate::leanh::lean_obj_tag(
                                                        v_quotContext_x3f_5285_,
                                                    ) == 0
                                                    {
                                                        v___x_5287_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5192_);
                                                        v_a_5288_ = crate::leanh::lean_ctor_get(
                                                            v___x_5287_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_a_5288_);
                                                        crate::leanh::lean_dec_ref(v___x_5287_);
                                                        v___y_4742_ = v___x_5286_;
                                                        v___y_4743_ = v___x_5193_;
                                                        v___y_4744_ = v_a_5280_;
                                                        v___y_4745_ = v_a_5284_;
                                                        v_a_4746_ = v_a_5288_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        v_val_5289_ = crate::leanh::lean_ctor_get(
                                                            v_quotContext_x3f_5285_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_5289_);
                                                        v___y_4742_ = v___x_5286_;
                                                        v___y_4743_ = v___x_5193_;
                                                        v___y_4744_ = v_a_5280_;
                                                        v___y_4745_ = v_a_5284_;
                                                        v_a_4746_ = v_val_5289_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_5282_);
                                                    crate::leanh::lean_dec(v_a_5280_);
                                                    crate::leanh::lean_dec(v___x_5193_);
                                                    crate::leanh::lean_dec(v_a_4366_);
                                                    crate::leanh::lean_dec(v_k_4356_);
                                                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                                                    v_a_5290_ =
                                                        crate::leanh::lean_ctor_get(v___x_5283_, 0);
                                                    v_isSharedCheck_5297_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5283_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5297_ == 0 {
                                                        v___x_5292_ = v___x_5283_;
                                                        v_isShared_5293_ = v_isSharedCheck_5297_;
                                                        state = 29;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5290_);
                                                        crate::leanh::lean_dec(v___x_5283_);
                                                        v___x_5292_ = crate::leanh::lean_box(0);
                                                        v_isShared_5293_ = v_isSharedCheck_5297_;
                                                        state = 29;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_5280_);
                                                crate::leanh::lean_dec(v___x_5193_);
                                                crate::leanh::lean_dec(v_a_4366_);
                                                crate::leanh::lean_dec(v_k_4356_);
                                                crate::leanh::lean_dec(v_doc_x3f_4353_);
                                                return v___x_5281_;
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v___x_5193_);
                                            crate::leanh::lean_dec(v_a_4366_);
                                            crate::leanh::lean_dec(v_k_4356_);
                                            crate::leanh::lean_dec(v_doc_x3f_4353_);
                                            v_a_5298_ = crate::leanh::lean_ctor_get(v___x_5279_, 0);
                                            v_isSharedCheck_5305_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5279_))
                                                    as u8;
                                            if v_isSharedCheck_5305_ == 0 {
                                                v___x_5300_ = v___x_5279_;
                                                v_isShared_5301_ = v_isSharedCheck_5305_;
                                                state = 31;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5298_);
                                                crate::leanh::lean_dec(v___x_5279_);
                                                v___x_5300_ = crate::leanh::lean_box(0);
                                                v_isShared_5301_ = v_isSharedCheck_5305_;
                                                state = 31;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_catName_5190_);
                                    v___y_5157_ = v___x_5265_;
                                    v___y_5158_ = v___x_5266_;
                                    v___y_5159_ = v___x_5193_;
                                    v___y_5160_ = v___y_5192_;
                                    v___y_5161_ = v___y_5191_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_catName_5190_);
                                v___y_5157_ = v___x_5265_;
                                v___y_5158_ = v___x_5266_;
                                v___y_5159_ = v___x_5193_;
                                v___y_5160_ = v___y_5192_;
                                v___y_5161_ = v___y_5191_;
                                state = 15;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_catName_5190_);
                            v___x_5306_ = l_Lean_Elab_Command_elabElabRulesAux___closed__74;
                            crate::leanh::lean_inc(v_k_4356_);
                            v___x_5307_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
                                v_k_4356_,
                                v_attrKind_4355_,
                                v_attrs_x3f_4354_,
                                v___x_5306_,
                                v___y_5191_,
                                v___y_5192_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5307_) == 0 {
                                v_a_5308_ = crate::leanh::lean_ctor_get(v___x_5307_, 0);
                                crate::leanh::lean_inc(v_a_5308_);
                                crate::leanh::lean_dec_ref_known(v___x_5307_, 1);
                                v___x_5309_ = l_Lean_Elab_Command_getRef___redArg(v___y_5191_);
                                if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
                                    v_a_5310_ = crate::leanh::lean_ctor_get(v___x_5309_, 0);
                                    crate::leanh::lean_inc(v_a_5310_);
                                    crate::leanh::lean_dec_ref_known(v___x_5309_, 1);
                                    v___x_5311_ =
                                        l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5191_);
                                    if crate::leanh::lean_obj_tag(v___x_5311_) == 0 {
                                        v_a_5312_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                                        crate::leanh::lean_inc(v_a_5312_);
                                        crate::leanh::lean_dec_ref_known(v___x_5311_, 1);
                                        v_quotContext_x3f_5313_ =
                                            crate::leanh::lean_ctor_get(v___y_5191_, 5);
                                        v___x_5314_ =
                                            l_Lean_SourceInfo_fromRef(v_a_5310_, v___x_5263_);
                                        crate::leanh::lean_dec(v_a_5310_);
                                        if crate::leanh::lean_obj_tag(v_quotContext_x3f_5313_) == 0
                                        {
                                            v___x_5315_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5192_);
                                            v_a_5316_ = crate::leanh::lean_ctor_get(v___x_5315_, 0);
                                            crate::leanh::lean_inc(v_a_5316_);
                                            crate::leanh::lean_dec_ref(v___x_5315_);
                                            v___y_4604_ = v___x_5314_;
                                            v___y_4605_ = v___x_5193_;
                                            v___y_4606_ = v_a_5312_;
                                            v___y_4607_ = v_a_5308_;
                                            v_a_4608_ = v_a_5316_;
                                            state = 6;
                                            continue;
                                        } else {
                                            v_val_5317_ = crate::leanh::lean_ctor_get(
                                                v_quotContext_x3f_5313_,
                                                0,
                                            );
                                            crate::leanh::lean_inc(v_val_5317_);
                                            v___y_4604_ = v___x_5314_;
                                            v___y_4605_ = v___x_5193_;
                                            v___y_4606_ = v_a_5312_;
                                            v___y_4607_ = v_a_5308_;
                                            v_a_4608_ = v_val_5317_;
                                            state = 6;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5310_);
                                        crate::leanh::lean_dec(v_a_5308_);
                                        crate::leanh::lean_dec(v___x_5193_);
                                        crate::leanh::lean_dec(v_a_4366_);
                                        crate::leanh::lean_dec(v_k_4356_);
                                        crate::leanh::lean_dec(v_doc_x3f_4353_);
                                        v_a_5318_ = crate::leanh::lean_ctor_get(v___x_5311_, 0);
                                        v_isSharedCheck_5325_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5311_)) as u8;
                                        if v_isSharedCheck_5325_ == 0 {
                                            v___x_5320_ = v___x_5311_;
                                            v_isShared_5321_ = v_isSharedCheck_5325_;
                                            state = 33;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5318_);
                                            crate::leanh::lean_dec(v___x_5311_);
                                            v___x_5320_ = crate::leanh::lean_box(0);
                                            v_isShared_5321_ = v_isSharedCheck_5325_;
                                            state = 33;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5308_);
                                    crate::leanh::lean_dec(v___x_5193_);
                                    crate::leanh::lean_dec(v_a_4366_);
                                    crate::leanh::lean_dec(v_k_4356_);
                                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                                    return v___x_5309_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_5193_);
                                crate::leanh::lean_dec(v_a_4366_);
                                crate::leanh::lean_dec(v_k_4356_);
                                crate::leanh::lean_dec(v_doc_x3f_4353_);
                                v_a_5326_ = crate::leanh::lean_ctor_get(v___x_5307_, 0);
                                v_isSharedCheck_5333_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5307_)) as u8;
                                if v_isSharedCheck_5333_ == 0 {
                                    v___x_5328_ = v___x_5307_;
                                    v_isShared_5329_ = v_isSharedCheck_5333_;
                                    state = 35;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5326_);
                                    crate::leanh::lean_dec(v___x_5307_);
                                    v___x_5328_ = crate::leanh::lean_box(0);
                                    v_isShared_5329_ = v_isSharedCheck_5333_;
                                    state = 35;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_catName_5190_);
                        v___x_5334_ = l_Lean_Elab_Command_elabElabRulesAux___closed__64;
                        crate::leanh::lean_inc(v_k_4356_);
                        v___x_5335_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0(
                            v_k_4356_,
                            v_attrKind_4355_,
                            v_attrs_x3f_4354_,
                            v___x_5334_,
                            v___y_5191_,
                            v___y_5192_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5335_) == 0 {
                            v_a_5336_ = crate::leanh::lean_ctor_get(v___x_5335_, 0);
                            crate::leanh::lean_inc(v_a_5336_);
                            crate::leanh::lean_dec_ref_known(v___x_5335_, 1);
                            v___x_5337_ = l_Lean_Elab_Command_getRef___redArg(v___y_5191_);
                            if crate::leanh::lean_obj_tag(v___x_5337_) == 0 {
                                v_a_5338_ = crate::leanh::lean_ctor_get(v___x_5337_, 0);
                                crate::leanh::lean_inc(v_a_5338_);
                                crate::leanh::lean_dec_ref_known(v___x_5337_, 1);
                                v___x_5339_ =
                                    l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5191_);
                                if crate::leanh::lean_obj_tag(v___x_5339_) == 0 {
                                    v_a_5340_ = crate::leanh::lean_ctor_get(v___x_5339_, 0);
                                    crate::leanh::lean_inc(v_a_5340_);
                                    crate::leanh::lean_dec_ref_known(v___x_5339_, 1);
                                    v_quotContext_x3f_5341_ =
                                        crate::leanh::lean_ctor_get(v___y_5191_, 5);
                                    v___x_5342_ = 0;
                                    v___x_5343_ = l_Lean_SourceInfo_fromRef(v_a_5338_, v___x_5342_);
                                    crate::leanh::lean_dec(v_a_5338_);
                                    if crate::leanh::lean_obj_tag(v_quotContext_x3f_5341_) == 0 {
                                        v___x_5344_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5192_);
                                        v_a_5345_ = crate::leanh::lean_ctor_get(v___x_5344_, 0);
                                        crate::leanh::lean_inc(v_a_5345_);
                                        crate::leanh::lean_dec_ref(v___x_5344_);
                                        v___y_4490_ = v___x_5193_;
                                        v___y_4491_ = v_a_5336_;
                                        v___y_4492_ = v_a_5340_;
                                        v___y_4493_ = v___x_5343_;
                                        v_a_4494_ = v_a_5345_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v_val_5346_ =
                                            crate::leanh::lean_ctor_get(v_quotContext_x3f_5341_, 0);
                                        crate::leanh::lean_inc(v_val_5346_);
                                        v___y_4490_ = v___x_5193_;
                                        v___y_4491_ = v_a_5336_;
                                        v___y_4492_ = v_a_5340_;
                                        v___y_4493_ = v___x_5343_;
                                        v_a_4494_ = v_val_5346_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5338_);
                                    crate::leanh::lean_dec(v_a_5336_);
                                    crate::leanh::lean_dec(v___x_5193_);
                                    crate::leanh::lean_del_object(v___x_4368_);
                                    crate::leanh::lean_dec(v_a_4366_);
                                    crate::leanh::lean_dec(v_k_4356_);
                                    crate::leanh::lean_dec(v_doc_x3f_4353_);
                                    v_a_5347_ = crate::leanh::lean_ctor_get(v___x_5339_, 0);
                                    v_isSharedCheck_5354_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5339_)) as u8;
                                    if v_isSharedCheck_5354_ == 0 {
                                        v___x_5349_ = v___x_5339_;
                                        v_isShared_5350_ = v_isSharedCheck_5354_;
                                        state = 37;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5347_);
                                        crate::leanh::lean_dec(v___x_5339_);
                                        v___x_5349_ = crate::leanh::lean_box(0);
                                        v_isShared_5350_ = v_isSharedCheck_5354_;
                                        state = 37;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5336_);
                                crate::leanh::lean_dec(v___x_5193_);
                                crate::leanh::lean_del_object(v___x_4368_);
                                crate::leanh::lean_dec(v_a_4366_);
                                crate::leanh::lean_dec(v_k_4356_);
                                crate::leanh::lean_dec(v_doc_x3f_4353_);
                                return v___x_5337_;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5193_);
                            crate::leanh::lean_del_object(v___x_4368_);
                            crate::leanh::lean_dec(v_a_4366_);
                            crate::leanh::lean_dec(v_k_4356_);
                            crate::leanh::lean_dec(v_doc_x3f_4353_);
                            v_a_5355_ = crate::leanh::lean_ctor_get(v___x_5335_, 0);
                            v_isSharedCheck_5362_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5335_)) as u8;
                            if v_isSharedCheck_5362_ == 0 {
                                v___x_5357_ = v___x_5335_;
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 39;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5355_);
                                crate::leanh::lean_dec(v___x_5335_);
                                v___x_5357_ = crate::leanh::lean_box(0);
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 39;
                                continue;
                            }
                        }
                    }
                }
            }
            21 => {
                if v_isShared_5220_ == 0 {
                    v___x_5222_ = v___x_5219_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5223_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5223_, 0, v_a_5217_);
                    v___x_5222_ = v_reuseFailAlloc_5223_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5222_;
            }
            23 => {
                if v_isShared_5228_ == 0 {
                    v___x_5230_ = v___x_5227_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5231_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5231_, 0, v_a_5225_);
                    v___x_5230_ = v_reuseFailAlloc_5231_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5230_;
            }
            25 => {
                if v_isShared_5249_ == 0 {
                    v___x_5251_ = v___x_5248_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5252_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5252_, 0, v_a_5246_);
                    v___x_5251_ = v_reuseFailAlloc_5252_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5251_;
            }
            27 => {
                if v_isShared_5257_ == 0 {
                    v___x_5259_ = v___x_5256_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
                    v___x_5259_ = v_reuseFailAlloc_5260_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5259_;
            }
            29 => {
                if v_isShared_5293_ == 0 {
                    v___x_5295_ = v___x_5292_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
                    v___x_5295_ = v_reuseFailAlloc_5296_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5295_;
            }
            31 => {
                if v_isShared_5301_ == 0 {
                    v___x_5303_ = v___x_5300_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5304_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5304_, 0, v_a_5298_);
                    v___x_5303_ = v_reuseFailAlloc_5304_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5303_;
            }
            33 => {
                if v_isShared_5321_ == 0 {
                    v___x_5323_ = v___x_5320_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
                    v___x_5323_ = v_reuseFailAlloc_5324_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5323_;
            }
            35 => {
                if v_isShared_5329_ == 0 {
                    v___x_5331_ = v___x_5328_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
                    v___x_5331_ = v_reuseFailAlloc_5332_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5331_;
            }
            37 => {
                if v_isShared_5350_ == 0 {
                    v___x_5352_ = v___x_5349_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5353_, 0, v_a_5347_);
                    v___x_5352_ = v_reuseFailAlloc_5353_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5352_;
            }
            39 => {
                if v_isShared_5358_ == 0 {
                    v___x_5360_ = v___x_5357_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5361_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
                    v___x_5360_ = v_reuseFailAlloc_5361_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5360_;
            }
            41 => {
                if v_isShared_5371_ == 0 {
                    v___x_5373_ = v___x_5370_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
                    v___x_5373_ = v_reuseFailAlloc_5374_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5373_;
            }
            43 => {
                if v_isShared_5380_ == 0 {
                    v___x_5382_ = v___x_5379_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 0, v_a_5377_);
                    v___x_5382_ = v_reuseFailAlloc_5383_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_5382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabElabRulesAux___boxed(
    mut v_doc_x3f_5385_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_5386_: *mut crate::leanh::LeanObject,
    mut v_attrKind_5387_: *mut crate::leanh::LeanObject,
    mut v_k_5388_: *mut crate::leanh::LeanObject,
    mut v_cat_x3f_5389_: *mut crate::leanh::LeanObject,
    mut v_expty_x3f_5390_: *mut crate::leanh::LeanObject,
    mut v_alts_5391_: *mut crate::leanh::LeanObject,
    mut v_a_5392_: *mut crate::leanh::LeanObject,
    mut v_a_5393_: *mut crate::leanh::LeanObject,
    mut v_a_5394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5395_ = l_Lean_Elab_Command_elabElabRulesAux(
        v_doc_x3f_5385_,
        v_attrs_x3f_5386_,
        v_attrKind_5387_,
        v_k_5388_,
        v_cat_x3f_5389_,
        v_expty_x3f_5390_,
        v_alts_5391_,
        v_a_5392_,
        v_a_5393_,
    );
    crate::leanh::lean_dec(v_a_5393_);
    crate::leanh::lean_dec_ref(v_a_5392_);
    crate::leanh::lean_dec(v_cat_x3f_5389_);
    crate::leanh::lean_dec(v_attrs_x3f_5386_);
    return v_res_5395_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(
    mut v_00_u03b1_5396_: *mut crate::leanh::LeanObject,
    mut v_ref_5397_: *mut crate::leanh::LeanObject,
    mut v_msg_5398_: *mut crate::leanh::LeanObject,
    mut v___y_5399_: *mut crate::leanh::LeanObject,
    mut v___y_5400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5402_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(
        v_ref_5397_,
        v_msg_5398_,
        v___y_5399_,
        v___y_5400_,
    );
    return v___x_5402_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___boxed(
    mut v_00_u03b1_5403_: *mut crate::leanh::LeanObject,
    mut v_ref_5404_: *mut crate::leanh::LeanObject,
    mut v_msg_5405_: *mut crate::leanh::LeanObject,
    mut v___y_5406_: *mut crate::leanh::LeanObject,
    mut v___y_5407_: *mut crate::leanh::LeanObject,
    mut v___y_5408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5409_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3(
        v_00_u03b1_5403_,
        v_ref_5404_,
        v_msg_5405_,
        v___y_5406_,
        v___y_5407_,
    );
    crate::leanh::lean_dec(v___y_5407_);
    crate::leanh::lean_dec_ref(v___y_5406_);
    crate::leanh::lean_dec(v_ref_5404_);
    return v_res_5409_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(
    mut v_msgData_5410_: *mut crate::leanh::LeanObject,
    mut v___y_5411_: *mut crate::leanh::LeanObject,
    mut v___y_5412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5414_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msgData_5410_, v___y_5412_);
    return v___x_5414_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___boxed(
    mut v_msgData_5415_: *mut crate::leanh::LeanObject,
    mut v___y_5416_: *mut crate::leanh::LeanObject,
    mut v___y_5417_: *mut crate::leanh::LeanObject,
    mut v___y_5418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5419_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6(v_msgData_5415_, v___y_5416_, v___y_5417_);
    crate::leanh::lean_dec(v___y_5417_);
    crate::leanh::lean_dec_ref(v___y_5416_);
    return v_res_5419_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(
    mut v_00_u03b1_5420_: *mut crate::leanh::LeanObject,
    mut v_msg_5421_: *mut crate::leanh::LeanObject,
    mut v___y_5422_: *mut crate::leanh::LeanObject,
    mut v___y_5423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5425_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___redArg(
        v_msg_5421_,
        v___y_5422_,
        v___y_5423_,
    );
    return v___x_5425_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6___boxed(
    mut v_00_u03b1_5426_: *mut crate::leanh::LeanObject,
    mut v_msg_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5431_ = l_Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6(
        v_00_u03b1_5426_,
        v_msg_5427_,
        v___y_5428_,
        v___y_5429_,
    );
    crate::leanh::lean_dec(v___y_5429_);
    crate::leanh::lean_dec_ref(v___y_5428_);
    return v_res_5431_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(
    mut v_msgData_5432_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5433_: *mut crate::leanh::LeanObject,
    mut v___y_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5437_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___redArg(v_msgData_5432_, v_macroStack_5433_, v___y_5435_);
    return v___x_5437_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7___boxed(
    mut v_msgData_5438_: *mut crate::leanh::LeanObject,
    mut v_macroStack_5439_: *mut crate::leanh::LeanObject,
    mut v___y_5440_: *mut crate::leanh::LeanObject,
    mut v___y_5441_: *mut crate::leanh::LeanObject,
    mut v___y_5442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5443_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__7(v_msgData_5438_, v_macroStack_5439_, v___y_5440_, v___y_5441_);
    crate::leanh::lean_dec(v___y_5441_);
    crate::leanh::lean_dec_ref(v___y_5440_);
    return v_res_5443_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___lam__0(
    mut v_x_5444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5445_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
    return v___x_5445_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___lam__0___boxed(
    mut v_x_5446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5447_ = l_Lean_Elab_Command_elabElabRules___lam__0(v_x_5446_);
    crate::leanh::lean_dec(v_x_5446_);
    return v_res_5447_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___lam__1(
    mut v___x_5452_: *mut crate::leanh::LeanObject,
    mut v___x_5453_: *mut crate::leanh::LeanObject,
    mut v_attrKind_5454_: *mut crate::leanh::LeanObject,
    mut v_expty_x3f_5455_: *mut crate::leanh::LeanObject,
    mut v___f_5456_: *mut crate::leanh::LeanObject,
    mut v_cat_x3f_5457_: *mut crate::leanh::LeanObject,
    mut v___x_5458_: *mut crate::leanh::LeanObject,
    mut v___x_5459_: *mut crate::leanh::LeanObject,
    mut v_attrs_x3f_5460_: *mut crate::leanh::LeanObject,
    mut v___x_5461_: *mut crate::leanh::LeanObject,
    mut v___x_5462_: *mut crate::leanh::LeanObject,
    mut v___x_5463_: *mut crate::leanh::LeanObject,
    mut v_doc_x3f_5464_: *mut crate::leanh::LeanObject,
    mut v_kind_x3f_5465_: *mut crate::leanh::LeanObject,
    mut v_alts_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
    mut v___y_5468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5475_: u8 = 0;
    let mut v_quotContext_x3f_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5477_: u8 = 0;
    let mut v___x_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_unused_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5576_: u8 = 0;
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_a_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5584_: u8 = 0;
    let mut v___x_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5470_ = l_Lean_Elab_Command_getRef___redArg(v___y_5467_);
                if crate::leanh::lean_obj_tag(v___x_5470_) == 0 {
                    v_a_5471_ = crate::leanh::lean_ctor_get(v___x_5470_, 0);
                    crate::leanh::lean_inc(v_a_5471_);
                    crate::leanh::lean_dec_ref_known(v___x_5470_, 1);
                    v___x_5472_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_5467_);
                    if crate::leanh::lean_obj_tag(v___x_5472_) == 0 {
                        v_isSharedCheck_5571_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5571_ == 0 {
                            v_unused_5572_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                            crate::leanh::lean_dec(v_unused_5572_);
                            v___x_5474_ = v___x_5472_;
                            v_isShared_5475_ = v_isSharedCheck_5571_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5472_);
                            v___x_5474_ = crate::leanh::lean_box(0);
                            v_isShared_5475_ = v_isSharedCheck_5571_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5471_);
                        crate::leanh::lean_dec(v_kind_x3f_5465_);
                        crate::leanh::lean_dec(v_doc_x3f_5464_);
                        crate::leanh::lean_dec_ref(v___x_5463_);
                        crate::leanh::lean_dec_ref(v___x_5462_);
                        crate::leanh::lean_dec_ref(v___x_5461_);
                        crate::leanh::lean_dec_ref(v___x_5458_);
                        crate::leanh::lean_dec(v_cat_x3f_5457_);
                        crate::leanh::lean_dec_ref(v___f_5456_);
                        crate::leanh::lean_dec(v_expty_x3f_5455_);
                        crate::leanh::lean_dec(v_attrKind_5454_);
                        crate::leanh::lean_dec(v___x_5453_);
                        crate::leanh::lean_dec(v___x_5452_);
                        v_a_5573_ = crate::leanh::lean_ctor_get(v___x_5472_, 0);
                        v_isSharedCheck_5580_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5472_)) as u8;
                        if v_isSharedCheck_5580_ == 0 {
                            v___x_5575_ = v___x_5472_;
                            v_isShared_5576_ = v_isSharedCheck_5580_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5573_);
                            crate::leanh::lean_dec(v___x_5472_);
                            v___x_5575_ = crate::leanh::lean_box(0);
                            v_isShared_5576_ = v_isSharedCheck_5580_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_kind_x3f_5465_);
                    crate::leanh::lean_dec(v_doc_x3f_5464_);
                    crate::leanh::lean_dec_ref(v___x_5463_);
                    crate::leanh::lean_dec_ref(v___x_5462_);
                    crate::leanh::lean_dec_ref(v___x_5461_);
                    crate::leanh::lean_dec_ref(v___x_5458_);
                    crate::leanh::lean_dec(v_cat_x3f_5457_);
                    crate::leanh::lean_dec_ref(v___f_5456_);
                    crate::leanh::lean_dec(v_expty_x3f_5455_);
                    crate::leanh::lean_dec(v_attrKind_5454_);
                    crate::leanh::lean_dec(v___x_5453_);
                    crate::leanh::lean_dec(v___x_5452_);
                    v_a_5581_ = crate::leanh::lean_ctor_get(v___x_5470_, 0);
                    v_isSharedCheck_5588_ = (!crate::leanh::lean_is_exclusive(v___x_5470_)) as u8;
                    if v_isSharedCheck_5588_ == 0 {
                        v___x_5583_ = v___x_5470_;
                        v_isShared_5584_ = v_isSharedCheck_5588_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5581_);
                        crate::leanh::lean_dec(v___x_5470_);
                        v___x_5583_ = crate::leanh::lean_box(0);
                        v_isShared_5584_ = v_isSharedCheck_5588_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v_quotContext_x3f_5476_ = crate::leanh::lean_ctor_get(v___y_5467_, 5);
                v___x_5477_ = 0;
                v___x_5478_ = l_Lean_SourceInfo_fromRef(v_a_5471_, v___x_5477_);
                crate::leanh::lean_dec(v_a_5471_);
                if crate::leanh::lean_obj_tag(v_quotContext_x3f_5476_) == 0 {
                    v___x_5570_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_5468_);
                    crate::leanh::lean_dec_ref(v___x_5570_);
                    state = 8;
                    continue;
                } else {
                    state = 8;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_5481_, 2);
                v___x_5488_ = l_Array_append___redArg(v___y_5481_, v___y_5487_);
                crate::leanh::lean_dec_ref(v___y_5487_);
                crate::leanh::lean_inc_n(v___y_5483_, 2);
                crate::leanh::lean_inc_n(v___x_5478_, 3);
                v___x_5489_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5489_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5489_, 1, v___y_5483_);
                crate::leanh::lean_ctor_set(v___x_5489_, 2, v___x_5488_);
                v___x_5490_ = l_Array_append___redArg(v___y_5481_, v_alts_5466_);
                v___x_5491_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5491_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5491_, 1, v___y_5483_);
                crate::leanh::lean_ctor_set(v___x_5491_, 2, v___x_5490_);
                v___x_5492_ = l_Lean_Syntax_node1(v___x_5478_, v___x_5452_, v___x_5491_);
                v___x_5493_ = l_Lean_Syntax_node8(
                    v___x_5478_,
                    v___x_5453_,
                    v___y_5486_,
                    v___y_5480_,
                    v_attrKind_5454_,
                    v___y_5482_,
                    v___y_5484_,
                    v___y_5485_,
                    v___x_5489_,
                    v___x_5492_,
                );
                if v_isShared_5475_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5474_, 0, v___x_5493_);
                    v___x_5495_ = v___x_5474_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5496_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5496_, 0, v___x_5493_);
                    v___x_5495_ = v_reuseFailAlloc_5496_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5495_;
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_5499_);
                v___x_5505_ = l_Array_append___redArg(v___y_5499_, v___y_5504_);
                crate::leanh::lean_dec_ref(v___y_5504_);
                crate::leanh::lean_inc(v___y_5501_);
                crate::leanh::lean_inc(v___x_5478_);
                v___x_5506_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5506_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5506_, 1, v___y_5501_);
                crate::leanh::lean_ctor_set(v___x_5506_, 2, v___x_5505_);
                if crate::leanh::lean_obj_tag(v_expty_x3f_5455_) == 1 {
                    crate::leanh::lean_dec_ref(v___f_5456_);
                    v_val_5507_ = crate::leanh::lean_ctor_get(v_expty_x3f_5455_, 0);
                    crate::leanh::lean_inc(v_val_5507_);
                    crate::leanh::lean_dec_ref_known(v_expty_x3f_5455_, 1);
                    v___x_5508_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__0;
                    crate::leanh::lean_inc(v___x_5478_);
                    v___x_5509_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5509_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5509_, 1, v___x_5508_);
                    v___x_5510_ = l_Array_mkArray2___redArg(v___x_5509_, v_val_5507_);
                    v___y_5480_ = v___y_5498_;
                    v___y_5481_ = v___y_5499_;
                    v___y_5482_ = v___y_5500_;
                    v___y_5483_ = v___y_5501_;
                    v___y_5484_ = v___y_5502_;
                    v___y_5485_ = v___x_5506_;
                    v___y_5486_ = v___y_5503_;
                    v___y_5487_ = v___x_5510_;
                    state = 2;
                    continue;
                } else {
                    v___x_5511_ = crate::leanh::lean_apply_1(v___f_5456_, v_expty_x3f_5455_);
                    v___y_5480_ = v___y_5498_;
                    v___y_5481_ = v___y_5499_;
                    v___y_5482_ = v___y_5500_;
                    v___y_5483_ = v___y_5501_;
                    v___y_5484_ = v___y_5502_;
                    v___y_5485_ = v___x_5506_;
                    v___y_5486_ = v___y_5503_;
                    v___y_5487_ = v___x_5511_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_5514_);
                v___x_5519_ = l_Array_append___redArg(v___y_5514_, v___y_5518_);
                crate::leanh::lean_dec_ref(v___y_5518_);
                crate::leanh::lean_inc(v___y_5516_);
                crate::leanh::lean_inc(v___x_5478_);
                v___x_5520_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5520_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5520_, 1, v___y_5516_);
                crate::leanh::lean_ctor_set(v___x_5520_, 2, v___x_5519_);
                if crate::leanh::lean_obj_tag(v_cat_x3f_5457_) == 1 {
                    v_val_5521_ = crate::leanh::lean_ctor_get(v_cat_x3f_5457_, 0);
                    crate::leanh::lean_inc(v_val_5521_);
                    crate::leanh::lean_dec_ref_known(v_cat_x3f_5457_, 1);
                    v___x_5522_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                    crate::leanh::lean_inc(v___x_5478_);
                    v___x_5523_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5523_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5523_, 1, v___x_5522_);
                    v___x_5524_ = l_Array_mkArray2___redArg(v___x_5523_, v_val_5521_);
                    v___y_5498_ = v___y_5513_;
                    v___y_5499_ = v___y_5514_;
                    v___y_5500_ = v___y_5515_;
                    v___y_5501_ = v___y_5516_;
                    v___y_5502_ = v___x_5520_;
                    v___y_5503_ = v___y_5517_;
                    v___y_5504_ = v___x_5524_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v___f_5456_);
                    v___x_5525_ = crate::leanh::lean_apply_1(v___f_5456_, v_cat_x3f_5457_);
                    v___y_5498_ = v___y_5513_;
                    v___y_5499_ = v___y_5514_;
                    v___y_5500_ = v___y_5515_;
                    v___y_5501_ = v___y_5516_;
                    v___y_5502_ = v___x_5520_;
                    v___y_5503_ = v___y_5517_;
                    v___y_5504_ = v___x_5525_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_5527_);
                v___x_5531_ = l_Array_append___redArg(v___y_5527_, v___y_5530_);
                crate::leanh::lean_dec_ref(v___y_5530_);
                crate::leanh::lean_inc(v___y_5528_);
                crate::leanh::lean_inc_n(v___x_5478_, 2);
                v___x_5532_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5532_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5532_, 1, v___y_5528_);
                crate::leanh::lean_ctor_set(v___x_5532_, 2, v___x_5531_);
                v___x_5533_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5533_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5533_, 1, v___x_5458_);
                if crate::leanh::lean_obj_tag(v_kind_x3f_5465_) == 0 {
                    v___x_5534_ = lean_mk_empty_array_with_capacity(v___x_5459_);
                    v___y_5513_ = v___x_5532_;
                    v___y_5514_ = v___y_5527_;
                    v___y_5515_ = v___x_5533_;
                    v___y_5516_ = v___y_5528_;
                    v___y_5517_ = v___y_5529_;
                    v___y_5518_ = v___x_5534_;
                    state = 5;
                    continue;
                } else {
                    v_val_5535_ = crate::leanh::lean_ctor_get(v_kind_x3f_5465_, 0);
                    crate::leanh::lean_inc(v_val_5535_);
                    crate::leanh::lean_dec_ref_known(v_kind_x3f_5465_, 1);
                    v___x_5536_ = lean_mk_syntax_ident(v_val_5535_);
                    v___x_5537_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__1;
                    crate::leanh::lean_inc_n(v___x_5478_, 4);
                    v___x_5538_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5538_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5538_, 1, v___x_5537_);
                    v___x_5539_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__2;
                    v___x_5540_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5540_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5540_, 1, v___x_5539_);
                    v___x_5541_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                    v___x_5542_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5542_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5542_, 1, v___x_5541_);
                    v___x_5543_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__3;
                    v___x_5544_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5544_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5544_, 1, v___x_5543_);
                    v___x_5545_ = l_Array_mkArray5___redArg(
                        v___x_5538_,
                        v___x_5540_,
                        v___x_5542_,
                        v___x_5536_,
                        v___x_5544_,
                    );
                    v___y_5513_ = v___x_5532_;
                    v___y_5514_ = v___y_5527_;
                    v___y_5515_ = v___x_5533_;
                    v___y_5516_ = v___y_5528_;
                    v___y_5517_ = v___y_5529_;
                    v___y_5518_ = v___x_5545_;
                    state = 5;
                    continue;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_5547_);
                v___x_5550_ = l_Array_append___redArg(v___y_5547_, v___y_5549_);
                crate::leanh::lean_dec_ref(v___y_5549_);
                crate::leanh::lean_inc(v___y_5548_);
                crate::leanh::lean_inc(v___x_5478_);
                v___x_5551_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5551_, 0, v___x_5478_);
                crate::leanh::lean_ctor_set(v___x_5551_, 1, v___y_5548_);
                crate::leanh::lean_ctor_set(v___x_5551_, 2, v___x_5550_);
                if crate::leanh::lean_obj_tag(v_attrs_x3f_5460_) == 1 {
                    v_val_5552_ = crate::leanh::lean_ctor_get(v_attrs_x3f_5460_, 0);
                    v___x_5553_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                    v___x_5554_ =
                        l_Lean_Name_mkStr4(v___x_5461_, v___x_5462_, v___x_5463_, v___x_5553_);
                    v___x_5555_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                    crate::leanh::lean_inc_n(v___x_5478_, 4);
                    v___x_5556_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5556_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5556_, 1, v___x_5555_);
                    crate::leanh::lean_inc_ref(v___y_5547_);
                    v___x_5557_ = l_Array_append___redArg(v___y_5547_, v_val_5552_);
                    crate::leanh::lean_inc(v___y_5548_);
                    v___x_5558_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5558_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5558_, 1, v___y_5548_);
                    crate::leanh::lean_ctor_set(v___x_5558_, 2, v___x_5557_);
                    v___x_5559_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                    v___x_5560_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5560_, 0, v___x_5478_);
                    crate::leanh::lean_ctor_set(v___x_5560_, 1, v___x_5559_);
                    v___x_5561_ = l_Lean_Syntax_node3(
                        v___x_5478_,
                        v___x_5554_,
                        v___x_5556_,
                        v___x_5558_,
                        v___x_5560_,
                    );
                    v___x_5562_ = l_Array_mkArray1___redArg(v___x_5561_);
                    v___y_5527_ = v___y_5547_;
                    v___y_5528_ = v___y_5548_;
                    v___y_5529_ = v___x_5551_;
                    v___y_5530_ = v___x_5562_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5463_);
                    crate::leanh::lean_dec_ref(v___x_5462_);
                    crate::leanh::lean_dec_ref(v___x_5461_);
                    v___x_5563_ = lean_mk_empty_array_with_capacity(v___x_5459_);
                    v___y_5527_ = v___y_5547_;
                    v___y_5528_ = v___y_5548_;
                    v___y_5529_ = v___x_5551_;
                    v___y_5530_ = v___x_5563_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v___x_5565_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_5566_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v_doc_x3f_5464_) == 1 {
                    v_val_5567_ = crate::leanh::lean_ctor_get(v_doc_x3f_5464_, 0);
                    crate::leanh::lean_inc(v_val_5567_);
                    crate::leanh::lean_dec_ref_known(v_doc_x3f_5464_, 1);
                    v___x_5568_ = l_Array_mkArray1___redArg(v_val_5567_);
                    v___y_5547_ = v___x_5566_;
                    v___y_5548_ = v___x_5565_;
                    v___y_5549_ = v___x_5568_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_doc_x3f_5464_);
                    v___x_5569_ = lean_mk_empty_array_with_capacity(v___x_5459_);
                    v___y_5547_ = v___x_5566_;
                    v___y_5548_ = v___x_5565_;
                    v___y_5549_ = v___x_5569_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v_isShared_5576_ == 0 {
                    v___x_5578_ = v___x_5575_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
                    v___x_5578_ = v_reuseFailAlloc_5579_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5578_;
            }
            11 => {
                if v_isShared_5584_ == 0 {
                    v___x_5586_ = v___x_5583_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
                    v___x_5586_ = v_reuseFailAlloc_5587_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5589_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5590_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_attrKind_5591_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_expty_x3f_5592_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___f_5593_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_cat_x3f_5594_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5595_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5596_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_attrs_x3f_5597_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5598_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5599_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_5600_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_doc_x3f_5601_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_kind_x3f_5602_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_alts_5603_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5604_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5605_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5606_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_5607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5607_ = l_Lean_Elab_Command_elabElabRules___lam__1(
        v___x_5589_,
        v___x_5590_,
        v_attrKind_5591_,
        v_expty_x3f_5592_,
        v___f_5593_,
        v_cat_x3f_5594_,
        v___x_5595_,
        v___x_5596_,
        v_attrs_x3f_5597_,
        v___x_5598_,
        v___x_5599_,
        v___x_5600_,
        v_doc_x3f_5601_,
        v_kind_x3f_5602_,
        v_alts_5603_,
        v___y_5604_,
        v___y_5605_,
    );
    crate::leanh::lean_dec(v___y_5605_);
    crate::leanh::lean_dec_ref(v___y_5604_);
    crate::leanh::lean_dec_ref(v_alts_5603_);
    crate::leanh::lean_dec(v_attrs_x3f_5597_);
    crate::leanh::lean_dec(v___x_5596_);
    return v_res_5607_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___lam__2(
    mut v___f_5636_: *mut crate::leanh::LeanObject,
    mut v_stx_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expty_x3f_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: u8 = 0;
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5669_: u8 = 0;
    let mut v___x_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5673_: u8 = 0;
    let mut v_a_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5677_: u8 = 0;
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5681_: u8 = 0;
    let mut v___y_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cat_x3f_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: u8 = 0;
    let mut v___x_5694_: u8 = 0;
    let mut v___x_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expty_x3f_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expty_x3f_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: u8 = 0;
    let mut v___x_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5724_: u8 = 0;
    let mut v___x_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5728_: u8 = 0;
    let mut v___y_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cat_x3f_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: u8 = 0;
    let mut v___x_5743_: u8 = 0;
    let mut v___x_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expty_x3f_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrKind_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: u8 = 0;
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: u8 = 0;
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5764_: u8 = 0;
    let mut v___x_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5769_: u8 = 0;
    let mut v___x_5770_: u8 = 0;
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cat_x3f_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    let mut v___x_5778_: u8 = 0;
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cat_x3f_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5789_: u8 = 0;
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: u8 = 0;
    let mut v___x_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: u8 = 0;
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5803_: u8 = 0;
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: u8 = 0;
    let mut v___x_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5641_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_5642_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_5643_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__0;
                v___x_5644_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__1;
                crate::leanh::lean_inc(v_stx_5637_);
                v___x_5645_ = l_Lean_Syntax_isOfKind(v_stx_5637_, v___x_5644_);
                if v___x_5645_ == 0 {
                    crate::leanh::lean_dec(v_stx_5637_);
                    crate::leanh::lean_dec_ref(v___f_5636_);
                    v___x_5646_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_5646_;
                } else {
                    v___x_5647_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5800_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5647_);
                    v___x_5801_ = l_Lean_Syntax_isNone(v___x_5800_);
                    if v___x_5801_ == 0 {
                        v___x_5802_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_5800_);
                        v___x_5803_ = l_Lean_Syntax_matchesNull(v___x_5800_, v___x_5802_);
                        if v___x_5803_ == 0 {
                            crate::leanh::lean_dec(v___x_5800_);
                            crate::leanh::lean_dec(v_stx_5637_);
                            crate::leanh::lean_dec_ref(v___f_5636_);
                            v___x_5804_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_5804_;
                        } else {
                            v_doc_x3f_5805_ = l_Lean_Syntax_getArg(v___x_5800_, v___x_5647_);
                            crate::leanh::lean_dec(v___x_5800_);
                            v___x_5806_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__7;
                            crate::leanh::lean_inc(v_doc_x3f_5805_);
                            v___x_5807_ = l_Lean_Syntax_isOfKind(v_doc_x3f_5805_, v___x_5806_);
                            if v___x_5807_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_5805_);
                                crate::leanh::lean_dec(v_stx_5637_);
                                crate::leanh::lean_dec_ref(v___f_5636_);
                                v___x_5808_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                                return v___x_5808_;
                            } else {
                                v___x_5809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5809_, 0, v_doc_x3f_5805_);
                                v_doc_x3f_5784_ = v___x_5809_;
                                v___y_5785_ = v___y_5638_;
                                v___y_5786_ = v___y_5639_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5800_);
                        v___x_5810_ = crate::leanh::lean_box(0);
                        v_doc_x3f_5784_ = v___x_5810_;
                        v___y_5785_ = v___y_5638_;
                        v___y_5786_ = v___y_5639_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5656_ = crate::leanh::lean_unsigned_to_nat(7);
                v___x_5657_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5656_);
                crate::leanh::lean_dec(v_stx_5637_);
                v___x_5658_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_5659_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__2;
                crate::leanh::lean_inc(v___x_5657_);
                v___x_5660_ = l_Lean_Syntax_isOfKind(v___x_5657_, v___x_5659_);
                if v___x_5660_ == 0 {
                    crate::leanh::lean_dec(v___x_5657_);
                    crate::leanh::lean_dec(v_expty_x3f_5655_);
                    crate::leanh::lean_dec(v___y_5654_);
                    crate::leanh::lean_dec(v___y_5653_);
                    crate::leanh::lean_dec(v___y_5650_);
                    crate::leanh::lean_dec(v___y_5649_);
                    crate::leanh::lean_dec_ref(v___f_5636_);
                    v___x_5661_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_5661_;
                } else {
                    v___f_5662_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Command_elabElabRules___lam__1___boxed
                            as *mut core::ffi::c_void,
                        18,
                        13,
                    );
                    crate::leanh::lean_closure_set(v___f_5662_, 0, v___x_5659_);
                    crate::leanh::lean_closure_set(v___f_5662_, 1, v___x_5644_);
                    crate::leanh::lean_closure_set(v___f_5662_, 2, v___y_5654_);
                    crate::leanh::lean_closure_set(v___f_5662_, 3, v_expty_x3f_5655_);
                    crate::leanh::lean_closure_set(v___f_5662_, 4, v___f_5636_);
                    crate::leanh::lean_closure_set(v___f_5662_, 5, v___y_5650_);
                    crate::leanh::lean_closure_set(v___f_5662_, 6, v___x_5643_);
                    crate::leanh::lean_closure_set(v___f_5662_, 7, v___x_5647_);
                    crate::leanh::lean_closure_set(v___f_5662_, 8, v___y_5653_);
                    crate::leanh::lean_closure_set(v___f_5662_, 9, v___x_5641_);
                    crate::leanh::lean_closure_set(v___f_5662_, 10, v___x_5642_);
                    crate::leanh::lean_closure_set(v___f_5662_, 11, v___x_5658_);
                    crate::leanh::lean_closure_set(v___f_5662_, 12, v___y_5649_);
                    v___x_5663_ = l_Lean_Syntax_getArg(v___x_5657_, v___x_5647_);
                    crate::leanh::lean_dec(v___x_5657_);
                    v_alts_5664_ = l_Lean_Syntax_getArgs(v___x_5663_);
                    crate::leanh::lean_dec(v___x_5663_);
                    v___x_5665_ = l_Lean_Elab_Command_expandNoKindMacroRulesAux(
                        v_alts_5664_,
                        v___x_5643_,
                        v___f_5662_,
                        v___y_5652_,
                        v___y_5651_,
                    );
                    crate::leanh::lean_dec_ref(v_alts_5664_);
                    if crate::leanh::lean_obj_tag(v___x_5665_) == 0 {
                        v_a_5666_ = crate::leanh::lean_ctor_get(v___x_5665_, 0);
                        v_isSharedCheck_5673_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5665_)) as u8;
                        if v_isSharedCheck_5673_ == 0 {
                            v___x_5668_ = v___x_5665_;
                            v_isShared_5669_ = v_isSharedCheck_5673_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5666_);
                            crate::leanh::lean_dec(v___x_5665_);
                            v___x_5668_ = crate::leanh::lean_box(0);
                            v_isShared_5669_ = v_isSharedCheck_5673_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_5674_ = crate::leanh::lean_ctor_get(v___x_5665_, 0);
                        v_isSharedCheck_5681_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5665_)) as u8;
                        if v_isSharedCheck_5681_ == 0 {
                            v___x_5676_ = v___x_5665_;
                            v_isShared_5677_ = v_isSharedCheck_5681_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5674_);
                            crate::leanh::lean_dec(v___x_5665_);
                            v___x_5676_ = crate::leanh::lean_box(0);
                            v_isShared_5677_ = v_isSharedCheck_5681_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_5669_ == 0 {
                    v___x_5671_ = v___x_5668_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5672_, 0, v_a_5666_);
                    v___x_5671_ = v_reuseFailAlloc_5672_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5671_;
            }
            4 => {
                if v_isShared_5677_ == 0 {
                    v___x_5679_ = v___x_5676_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5680_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5680_, 0, v_a_5674_);
                    v___x_5679_ = v_reuseFailAlloc_5680_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5679_;
            }
            6 => {
                v___x_5691_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_5692_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5691_);
                v___x_5693_ = l_Lean_Syntax_isNone(v___x_5692_);
                if v___x_5693_ == 0 {
                    crate::leanh::lean_inc(v___x_5692_);
                    v___x_5694_ = l_Lean_Syntax_matchesNull(v___x_5692_, v___y_5686_);
                    if v___x_5694_ == 0 {
                        crate::leanh::lean_dec(v___x_5692_);
                        crate::leanh::lean_dec(v_cat_x3f_5688_);
                        crate::leanh::lean_dec(v___y_5685_);
                        crate::leanh::lean_dec(v___y_5684_);
                        crate::leanh::lean_dec(v___y_5683_);
                        crate::leanh::lean_dec(v_stx_5637_);
                        crate::leanh::lean_dec_ref(v___f_5636_);
                        v___x_5695_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_5695_;
                    } else {
                        v_expty_x3f_5696_ = l_Lean_Syntax_getArg(v___x_5692_, v___y_5687_);
                        crate::leanh::lean_dec(v___x_5692_);
                        v___x_5697_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5697_, 0, v_expty_x3f_5696_);
                        v___y_5649_ = v___y_5683_;
                        v___y_5650_ = v_cat_x3f_5688_;
                        v___y_5651_ = v___y_5690_;
                        v___y_5652_ = v___y_5689_;
                        v___y_5653_ = v___y_5684_;
                        v___y_5654_ = v___y_5685_;
                        v_expty_x3f_5655_ = v___x_5697_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5692_);
                    v___x_5698_ = crate::leanh::lean_box(0);
                    v___y_5649_ = v___y_5683_;
                    v___y_5650_ = v_cat_x3f_5688_;
                    v___y_5651_ = v___y_5690_;
                    v___y_5652_ = v___y_5689_;
                    v___y_5653_ = v___y_5684_;
                    v___y_5654_ = v___y_5685_;
                    v_expty_x3f_5655_ = v___x_5698_;
                    state = 1;
                    continue;
                }
            }
            7 => {
                v___x_5709_ = crate::leanh::lean_unsigned_to_nat(7);
                v___x_5710_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5709_);
                crate::leanh::lean_dec(v_stx_5637_);
                v___x_5711_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                crate::leanh::lean_inc_ref(v___y_5701_);
                v___x_5712_ =
                    l_Lean_Name_mkStr4(v___x_5641_, v___x_5642_, v___y_5701_, v___x_5711_);
                crate::leanh::lean_inc(v___x_5710_);
                v___x_5713_ = l_Lean_Syntax_isOfKind(v___x_5710_, v___x_5712_);
                crate::leanh::lean_dec(v___x_5712_);
                if v___x_5713_ == 0 {
                    crate::leanh::lean_dec(v___x_5710_);
                    crate::leanh::lean_dec(v_expty_x3f_5706_);
                    crate::leanh::lean_dec(v___y_5705_);
                    crate::leanh::lean_dec(v___y_5704_);
                    crate::leanh::lean_dec(v___y_5703_);
                    crate::leanh::lean_dec(v___y_5702_);
                    crate::leanh::lean_dec(v___y_5700_);
                    v___x_5714_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_5714_;
                } else {
                    v___x_5715_ = l_Lean_TSyntax_getId(v___y_5702_);
                    crate::leanh::lean_dec(v___y_5702_);
                    v___x_5716_ = l_Lean_Elab_Command_resolveSyntaxKind(
                        v___x_5715_,
                        v___y_5707_,
                        v___y_5708_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5716_) == 0 {
                        v_a_5717_ = crate::leanh::lean_ctor_get(v___x_5716_, 0);
                        crate::leanh::lean_inc(v_a_5717_);
                        crate::leanh::lean_dec_ref_known(v___x_5716_, 1);
                        v___x_5718_ = l_Lean_Syntax_getArg(v___x_5710_, v___x_5647_);
                        crate::leanh::lean_dec(v___x_5710_);
                        v_alts_5719_ = l_Lean_Syntax_getArgs(v___x_5718_);
                        crate::leanh::lean_dec(v___x_5718_);
                        v___x_5720_ = l_Lean_Elab_Command_elabElabRulesAux(
                            v___y_5700_,
                            v___y_5703_,
                            v___y_5704_,
                            v_a_5717_,
                            v___y_5705_,
                            v_expty_x3f_5706_,
                            v_alts_5719_,
                            v___y_5707_,
                            v___y_5708_,
                        );
                        crate::leanh::lean_dec(v___y_5705_);
                        crate::leanh::lean_dec(v___y_5703_);
                        return v___x_5720_;
                    } else {
                        crate::leanh::lean_dec(v___x_5710_);
                        crate::leanh::lean_dec(v_expty_x3f_5706_);
                        crate::leanh::lean_dec(v___y_5705_);
                        crate::leanh::lean_dec(v___y_5704_);
                        crate::leanh::lean_dec(v___y_5703_);
                        crate::leanh::lean_dec(v___y_5700_);
                        v_a_5721_ = crate::leanh::lean_ctor_get(v___x_5716_, 0);
                        v_isSharedCheck_5728_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5716_)) as u8;
                        if v_isSharedCheck_5728_ == 0 {
                            v___x_5723_ = v___x_5716_;
                            v_isShared_5724_ = v_isSharedCheck_5728_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5721_);
                            crate::leanh::lean_dec(v___x_5716_);
                            v___x_5723_ = crate::leanh::lean_box(0);
                            v_isShared_5724_ = v_isSharedCheck_5728_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            8 => {
                if v_isShared_5724_ == 0 {
                    v___x_5726_ = v___x_5723_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5727_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5727_, 0, v_a_5721_);
                    v___x_5726_ = v_reuseFailAlloc_5727_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5726_;
            }
            10 => {
                v___x_5740_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_5741_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5740_);
                v___x_5742_ = l_Lean_Syntax_isNone(v___x_5741_);
                if v___x_5742_ == 0 {
                    crate::leanh::lean_inc(v___x_5741_);
                    v___x_5743_ = l_Lean_Syntax_matchesNull(v___x_5741_, v___y_5734_);
                    if v___x_5743_ == 0 {
                        crate::leanh::lean_dec(v___x_5741_);
                        crate::leanh::lean_dec(v_cat_x3f_5737_);
                        crate::leanh::lean_dec(v___y_5735_);
                        crate::leanh::lean_dec(v___y_5733_);
                        crate::leanh::lean_dec(v___y_5732_);
                        crate::leanh::lean_dec(v___y_5730_);
                        crate::leanh::lean_dec(v_stx_5637_);
                        v___x_5744_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_5744_;
                    } else {
                        v_expty_x3f_5745_ = l_Lean_Syntax_getArg(v___x_5741_, v___y_5736_);
                        crate::leanh::lean_dec(v___x_5741_);
                        v___x_5746_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5746_, 0, v_expty_x3f_5745_);
                        v___y_5700_ = v___y_5730_;
                        v___y_5701_ = v___y_5731_;
                        v___y_5702_ = v___y_5732_;
                        v___y_5703_ = v___y_5733_;
                        v___y_5704_ = v___y_5735_;
                        v___y_5705_ = v_cat_x3f_5737_;
                        v_expty_x3f_5706_ = v___x_5746_;
                        v___y_5707_ = v___y_5738_;
                        v___y_5708_ = v___y_5739_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5741_);
                    v___x_5747_ = crate::leanh::lean_box(0);
                    v___y_5700_ = v___y_5730_;
                    v___y_5701_ = v___y_5731_;
                    v___y_5702_ = v___y_5732_;
                    v___y_5703_ = v___y_5733_;
                    v___y_5704_ = v___y_5735_;
                    v___y_5705_ = v_cat_x3f_5737_;
                    v_expty_x3f_5706_ = v___x_5747_;
                    v___y_5707_ = v___y_5738_;
                    v___y_5708_ = v___y_5739_;
                    state = 7;
                    continue;
                }
            }
            11 => {
                v___x_5754_ = crate::leanh::lean_unsigned_to_nat(2);
                v_attrKind_5755_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5754_);
                v___x_5756_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_5757_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__4;
                crate::leanh::lean_inc(v_attrKind_5755_);
                v___x_5758_ = l_Lean_Syntax_isOfKind(v_attrKind_5755_, v___x_5757_);
                if v___x_5758_ == 0 {
                    crate::leanh::lean_dec(v_attrKind_5755_);
                    crate::leanh::lean_dec(v_attrs_x3f_5753_);
                    crate::leanh::lean_dec(v___y_5749_);
                    crate::leanh::lean_dec(v_stx_5637_);
                    crate::leanh::lean_dec_ref(v___f_5636_);
                    v___x_5759_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_5759_;
                } else {
                    v___x_5760_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5761_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5760_);
                    crate::leanh::lean_inc(v___x_5761_);
                    v___x_5762_ = l_Lean_Syntax_matchesNull(v___x_5761_, v___x_5647_);
                    if v___x_5762_ == 0 {
                        crate::leanh::lean_dec_ref(v___f_5636_);
                        v___x_5763_ = crate::leanh::lean_unsigned_to_nat(5);
                        crate::leanh::lean_inc(v___x_5761_);
                        v___x_5764_ = l_Lean_Syntax_matchesNull(v___x_5761_, v___x_5763_);
                        if v___x_5764_ == 0 {
                            crate::leanh::lean_dec(v___x_5761_);
                            crate::leanh::lean_dec(v_attrKind_5755_);
                            crate::leanh::lean_dec(v_attrs_x3f_5753_);
                            crate::leanh::lean_dec(v___y_5749_);
                            crate::leanh::lean_dec(v_stx_5637_);
                            v___x_5765_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_5765_;
                        } else {
                            v___x_5766_ = crate::leanh::lean_unsigned_to_nat(3);
                            v_kind_5767_ = l_Lean_Syntax_getArg(v___x_5761_, v___x_5766_);
                            crate::leanh::lean_dec(v___x_5761_);
                            v___x_5768_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5763_);
                            v___x_5769_ = l_Lean_Syntax_isNone(v___x_5768_);
                            if v___x_5769_ == 0 {
                                crate::leanh::lean_inc(v___x_5768_);
                                v___x_5770_ = l_Lean_Syntax_matchesNull(v___x_5768_, v___x_5754_);
                                if v___x_5770_ == 0 {
                                    crate::leanh::lean_dec(v___x_5768_);
                                    crate::leanh::lean_dec(v_kind_5767_);
                                    crate::leanh::lean_dec(v_attrKind_5755_);
                                    crate::leanh::lean_dec(v_attrs_x3f_5753_);
                                    crate::leanh::lean_dec(v___y_5749_);
                                    crate::leanh::lean_dec(v_stx_5637_);
                                    v___x_5771_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                                    return v___x_5771_;
                                } else {
                                    v_cat_x3f_5772_ =
                                        l_Lean_Syntax_getArg(v___x_5768_, v___y_5752_);
                                    crate::leanh::lean_dec(v___x_5768_);
                                    v___x_5773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_5773_, 0, v_cat_x3f_5772_);
                                    v___y_5730_ = v___y_5749_;
                                    v___y_5731_ = v___x_5756_;
                                    v___y_5732_ = v_kind_5767_;
                                    v___y_5733_ = v_attrs_x3f_5753_;
                                    v___y_5734_ = v___x_5754_;
                                    v___y_5735_ = v_attrKind_5755_;
                                    v___y_5736_ = v___y_5752_;
                                    v_cat_x3f_5737_ = v___x_5773_;
                                    v___y_5738_ = v___y_5751_;
                                    v___y_5739_ = v___y_5750_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_5768_);
                                v___x_5774_ = crate::leanh::lean_box(0);
                                v___y_5730_ = v___y_5749_;
                                v___y_5731_ = v___x_5756_;
                                v___y_5732_ = v_kind_5767_;
                                v___y_5733_ = v_attrs_x3f_5753_;
                                v___y_5734_ = v___x_5754_;
                                v___y_5735_ = v_attrKind_5755_;
                                v___y_5736_ = v___y_5752_;
                                v_cat_x3f_5737_ = v___x_5774_;
                                v___y_5738_ = v___y_5751_;
                                v___y_5739_ = v___y_5750_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5761_);
                        v___x_5775_ = crate::leanh::lean_unsigned_to_nat(5);
                        v___x_5776_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5775_);
                        v___x_5777_ = l_Lean_Syntax_isNone(v___x_5776_);
                        if v___x_5777_ == 0 {
                            crate::leanh::lean_inc(v___x_5776_);
                            v___x_5778_ = l_Lean_Syntax_matchesNull(v___x_5776_, v___x_5754_);
                            if v___x_5778_ == 0 {
                                crate::leanh::lean_dec(v___x_5776_);
                                crate::leanh::lean_dec(v_attrKind_5755_);
                                crate::leanh::lean_dec(v_attrs_x3f_5753_);
                                crate::leanh::lean_dec(v___y_5749_);
                                crate::leanh::lean_dec(v_stx_5637_);
                                crate::leanh::lean_dec_ref(v___f_5636_);
                                v___x_5779_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                                return v___x_5779_;
                            } else {
                                v_cat_x3f_5780_ = l_Lean_Syntax_getArg(v___x_5776_, v___y_5752_);
                                crate::leanh::lean_dec(v___x_5776_);
                                v___x_5781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5781_, 0, v_cat_x3f_5780_);
                                v___y_5683_ = v___y_5749_;
                                v___y_5684_ = v_attrs_x3f_5753_;
                                v___y_5685_ = v_attrKind_5755_;
                                v___y_5686_ = v___x_5754_;
                                v___y_5687_ = v___y_5752_;
                                v_cat_x3f_5688_ = v___x_5781_;
                                v___y_5689_ = v___y_5751_;
                                v___y_5690_ = v___y_5750_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_5776_);
                            v___x_5782_ = crate::leanh::lean_box(0);
                            v___y_5683_ = v___y_5749_;
                            v___y_5684_ = v_attrs_x3f_5753_;
                            v___y_5685_ = v_attrKind_5755_;
                            v___y_5686_ = v___x_5754_;
                            v___y_5687_ = v___y_5752_;
                            v_cat_x3f_5688_ = v___x_5782_;
                            v___y_5689_ = v___y_5751_;
                            v___y_5690_ = v___y_5750_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            12 => {
                v___x_5787_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5788_ = l_Lean_Syntax_getArg(v_stx_5637_, v___x_5787_);
                v___x_5789_ = l_Lean_Syntax_isNone(v___x_5788_);
                if v___x_5789_ == 0 {
                    crate::leanh::lean_inc(v___x_5788_);
                    v___x_5790_ = l_Lean_Syntax_matchesNull(v___x_5788_, v___x_5787_);
                    if v___x_5790_ == 0 {
                        crate::leanh::lean_dec(v___x_5788_);
                        crate::leanh::lean_dec(v_doc_x3f_5784_);
                        crate::leanh::lean_dec(v_stx_5637_);
                        crate::leanh::lean_dec_ref(v___f_5636_);
                        v___x_5791_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_5791_;
                    } else {
                        v___x_5792_ = l_Lean_Syntax_getArg(v___x_5788_, v___x_5647_);
                        crate::leanh::lean_dec(v___x_5788_);
                        v___x_5793_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__5;
                        crate::leanh::lean_inc(v___x_5792_);
                        v___x_5794_ = l_Lean_Syntax_isOfKind(v___x_5792_, v___x_5793_);
                        if v___x_5794_ == 0 {
                            crate::leanh::lean_dec(v___x_5792_);
                            crate::leanh::lean_dec(v_doc_x3f_5784_);
                            crate::leanh::lean_dec(v_stx_5637_);
                            crate::leanh::lean_dec_ref(v___f_5636_);
                            v___x_5795_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_5795_;
                        } else {
                            v___x_5796_ = l_Lean_Syntax_getArg(v___x_5792_, v___x_5787_);
                            crate::leanh::lean_dec(v___x_5792_);
                            v_attrs_x3f_5797_ = l_Lean_Syntax_getArgs(v___x_5796_);
                            crate::leanh::lean_dec(v___x_5796_);
                            v___x_5798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5798_, 0, v_attrs_x3f_5797_);
                            v___y_5749_ = v_doc_x3f_5784_;
                            v___y_5750_ = v___y_5786_;
                            v___y_5751_ = v___y_5785_;
                            v___y_5752_ = v___x_5787_;
                            v_attrs_x3f_5753_ = v___x_5798_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5788_);
                    v___x_5799_ = crate::leanh::lean_box(0);
                    v___y_5749_ = v_doc_x3f_5784_;
                    v___y_5750_ = v___y_5786_;
                    v___y_5751_ = v___y_5785_;
                    v___y_5752_ = v___x_5787_;
                    v_attrs_x3f_5753_ = v___x_5799_;
                    state = 11;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___lam__2___boxed(
    mut v___f_5811_: *mut crate::leanh::LeanObject,
    mut v_stx_5812_: *mut crate::leanh::LeanObject,
    mut v___y_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5816_ = l_Lean_Elab_Command_elabElabRules___lam__2(
        v___f_5811_,
        v_stx_5812_,
        v___y_5813_,
        v___y_5814_,
    );
    crate::leanh::lean_dec(v___y_5814_);
    crate::leanh::lean_dec_ref(v___y_5813_);
    return v_res_5816_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules(
    mut v_a_5820_: *mut crate::leanh::LeanObject,
    mut v_a_5821_: *mut crate::leanh::LeanObject,
    mut v_a_5822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_5824_ = l_Lean_Elab_Command_elabElabRules___closed__1;
    v___x_5825_ = l_Lean_Elab_Command_adaptExpander(v___f_5824_, v_a_5820_, v_a_5821_, v_a_5822_);
    return v___x_5825_;
}
pub unsafe fn l_Lean_Elab_Command_elabElabRules___boxed(
    mut v_a_5826_: *mut crate::leanh::LeanObject,
    mut v_a_5827_: *mut crate::leanh::LeanObject,
    mut v_a_5828_: *mut crate::leanh::LeanObject,
    mut v_a_5829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5830_ = l_Lean_Elab_Command_elabElabRules(v_a_5826_, v_a_5827_, v_a_5828_);
    crate::leanh::lean_dec(v_a_5828_);
    crate::leanh::lean_dec_ref(v_a_5827_);
    return v_res_5830_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5838_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_5839_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__1;
    v___x_5840_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1;
    v___x_5841_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabElabRules___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_5842_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5838_,
        v___x_5839_,
        v___x_5840_,
        v___x_5841_,
    );
    return v___x_5842_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___boxed(
    mut v_a_5843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5844_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
    return v_res_5844_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5871_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1___closed__1;
    v___x_5872_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___closed__6;
    v___x_5873_ = l_Lean_addBuiltinDeclarationRanges(v___x_5871_, v___x_5872_);
    return v___x_5873_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3___boxed(
    mut v_a_5874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5875_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
    return v_res_5875_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(
    mut v_sz_5876_: usize,
    mut v_i_5877_: usize,
    mut v_bs_5878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5879_: u8 = 0;
    let mut v_v_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: usize = 0;
    let mut v___x_5884_: usize = 0;
    let mut v___x_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5879_ = lean_usize_dec_lt(v_i_5877_, v_sz_5876_);
                if v___x_5879_ == 0 {
                    return v_bs_5878_;
                } else {
                    v_v_5880_ = lean_array_uget(v_bs_5878_, v_i_5877_);
                    v___x_5881_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5882_ = lean_array_uset(v_bs_5878_, v_i_5877_, v___x_5881_);
                    v___x_5883_ = 1usize;
                    v___x_5884_ = lean_usize_add(v_i_5877_, v___x_5883_);
                    v___x_5885_ = lean_array_uset(v_bs_x27_5882_, v_i_5877_, v_v_5880_);
                    v_i_5877_ = v___x_5884_;
                    v_bs_5878_ = v___x_5885_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2___boxed(
    mut v_sz_5887_: *mut crate::leanh::LeanObject,
    mut v_i_5888_: *mut crate::leanh::LeanObject,
    mut v_bs_5889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5890_: usize = 0;
    let mut v_i_boxed_5891_: usize = 0;
    let mut v_res_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5890_ = crate::leanh::lean_unbox_usize(v_sz_5887_);
    crate::leanh::lean_dec(v_sz_5887_);
    v_i_boxed_5891_ = crate::leanh::lean_unbox_usize(v_i_5888_);
    crate::leanh::lean_dec(v_i_5888_);
    v_res_5892_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_boxed_5890_, v_i_boxed_5891_, v_bs_5889_);
    return v_res_5892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(
    mut v_sz_5893_: usize,
    mut v_i_5894_: usize,
    mut v_bs_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
    mut v___y_5897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5899_: u8 = 0;
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: usize = 0;
    let mut v___x_5907_: usize = 0;
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5913_: u8 = 0;
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5899_ = lean_usize_dec_lt(v_i_5894_, v_sz_5893_);
                if v___x_5899_ == 0 {
                    v___x_5900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5900_, 0, v_bs_5895_);
                    return v___x_5900_;
                } else {
                    v_v_5901_ = lean_array_uget_borrowed(v_bs_5895_, v_i_5894_);
                    crate::leanh::lean_inc(v_v_5901_);
                    v___x_5902_ =
                        l_Lean_Elab_Command_expandMacroArg(v_v_5901_, v___y_5896_, v___y_5897_);
                    if crate::leanh::lean_obj_tag(v___x_5902_) == 0 {
                        v_a_5903_ = crate::leanh::lean_ctor_get(v___x_5902_, 0);
                        crate::leanh::lean_inc(v_a_5903_);
                        crate::leanh::lean_dec_ref_known(v___x_5902_, 1);
                        v___x_5904_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_5905_ = lean_array_uset(v_bs_5895_, v_i_5894_, v___x_5904_);
                        v___x_5906_ = 1usize;
                        v___x_5907_ = lean_usize_add(v_i_5894_, v___x_5906_);
                        v___x_5908_ = lean_array_uset(v_bs_x27_5905_, v_i_5894_, v_a_5903_);
                        v_i_5894_ = v___x_5907_;
                        v_bs_5895_ = v___x_5908_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_5895_);
                        v_a_5910_ = crate::leanh::lean_ctor_get(v___x_5902_, 0);
                        v_isSharedCheck_5917_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5902_)) as u8;
                        if v_isSharedCheck_5917_ == 0 {
                            v___x_5912_ = v___x_5902_;
                            v_isShared_5913_ = v_isSharedCheck_5917_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5910_);
                            crate::leanh::lean_dec(v___x_5902_);
                            v___x_5912_ = crate::leanh::lean_box(0);
                            v_isShared_5913_ = v_isSharedCheck_5917_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5913_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_a_5910_);
                    v___x_5915_ = v_reuseFailAlloc_5916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1___boxed(
    mut v_sz_5918_: *mut crate::leanh::LeanObject,
    mut v_i_5919_: *mut crate::leanh::LeanObject,
    mut v_bs_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5924_: usize = 0;
    let mut v_i_boxed_5925_: usize = 0;
    let mut v_res_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5924_ = crate::leanh::lean_unbox_usize(v_sz_5918_);
    crate::leanh::lean_dec(v_sz_5918_);
    v_i_boxed_5925_ = crate::leanh::lean_unbox_usize(v_i_5919_);
    crate::leanh::lean_dec(v_i_5919_);
    v_res_5926_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_boxed_5924_, v_i_boxed_5925_, v_bs_5920_, v___y_5921_, v___y_5922_);
    crate::leanh::lean_dec(v___y_5922_);
    crate::leanh::lean_dec_ref(v___y_5921_);
    return v_res_5926_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(
    mut v_keys_5927_: *mut crate::leanh::LeanObject,
    mut v_i_5928_: *mut crate::leanh::LeanObject,
    mut v_k_5929_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: u8 = 0;
    let mut v_k_x27_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5933_: u8 = 0;
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5930_ = lean_array_get_size(v_keys_5927_);
                v___x_5931_ = lean_nat_dec_lt(v_i_5928_, v___x_5930_);
                if v___x_5931_ == 0 {
                    crate::leanh::lean_dec(v_i_5928_);
                    return v___x_5931_;
                } else {
                    v_k_x27_5932_ = lean_array_fget_borrowed(v_keys_5927_, v_i_5928_);
                    v___x_5933_ = l_Lean_instBEqExtraModUse_beq(v_k_5929_, v_k_x27_5932_);
                    if v___x_5933_ == 0 {
                        v___x_5934_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5935_ = lean_nat_add(v_i_5928_, v___x_5934_);
                        crate::leanh::lean_dec(v_i_5928_);
                        v_i_5928_ = v___x_5935_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_5928_);
                        return v___x_5933_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg___boxed(
    mut v_keys_5937_: *mut crate::leanh::LeanObject,
    mut v_i_5938_: *mut crate::leanh::LeanObject,
    mut v_k_5939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5940_: u8 = 0;
    let mut v_r_5941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5940_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_5937_, v_i_5938_, v_k_5939_);
    crate::leanh::lean_dec_ref(v_k_5939_);
    crate::leanh::lean_dec_ref(v_keys_5937_);
    v_r_5941_ = crate::leanh::lean_box((v_res_5940_) as usize);
    return v_r_5941_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0()
-> usize {
    let mut v___x_5942_: usize = 0;
    let mut v___x_5943_: usize = 0;
    let mut v___x_5944_: usize = 0;
    v___x_5942_ = 5usize;
    v___x_5943_ = 1usize;
    v___x_5944_ = lean_usize_shift_left(v___x_5943_, v___x_5942_);
    return v___x_5944_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1()
-> usize {
    let mut v___x_5945_: usize = 0;
    let mut v___x_5946_: usize = 0;
    let mut v___x_5947_: usize = 0;
    v___x_5945_ = 1usize;
    v___x_5946_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__0);
    v___x_5947_ = lean_usize_sub(v___x_5946_, v___x_5945_);
    return v___x_5947_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(
    mut v_x_5948_: *mut crate::leanh::LeanObject,
    mut v_x_5949_: usize,
    mut v_x_5950_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: usize = 0;
    let mut v___x_5954_: usize = 0;
    let mut v___x_5955_: usize = 0;
    let mut v_j_5956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5959_: u8 = 0;
    let mut v_node_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5961_: usize = 0;
    let mut v___x_5963_: u8 = 0;
    let mut v_ks_5964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5948_) == 0 {
                    v_es_5951_ = crate::leanh::lean_ctor_get(v_x_5948_, 0);
                    v___x_5952_ = crate::leanh::lean_box(2);
                    v___x_5953_ = 5usize;
                    v___x_5954_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___closed__1);
                    v___x_5955_ = lean_usize_land(v_x_5949_, v___x_5954_);
                    v_j_5956_ = lean_usize_to_nat(v___x_5955_);
                    v___x_5957_ = lean_array_get_borrowed(v___x_5952_, v_es_5951_, v_j_5956_);
                    crate::leanh::lean_dec(v_j_5956_);
                    match crate::leanh::lean_obj_tag(v___x_5957_) {
                        0 => {
                            v_key_5958_ = crate::leanh::lean_ctor_get(v___x_5957_, 0);
                            v___x_5959_ = l_Lean_instBEqExtraModUse_beq(v_x_5950_, v_key_5958_);
                            return v___x_5959_;
                        }
                        1 => {
                            v_node_5960_ = crate::leanh::lean_ctor_get(v___x_5957_, 0);
                            v___x_5961_ = lean_usize_shift_right(v_x_5949_, v___x_5953_);
                            v_x_5948_ = v_node_5960_;
                            v_x_5949_ = v___x_5961_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_5963_ = 0;
                            return v___x_5963_;
                        }
                    }
                } else {
                    v_ks_5964_ = crate::leanh::lean_ctor_get(v_x_5948_, 0);
                    v___x_5965_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5966_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_ks_5964_, v___x_5965_, v_x_5950_);
                    return v___x_5966_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg___boxed(
    mut v_x_5967_: *mut crate::leanh::LeanObject,
    mut v_x_5968_: *mut crate::leanh::LeanObject,
    mut v_x_5969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_19445__boxed_5970_: usize = 0;
    let mut v_res_5971_: u8 = 0;
    let mut v_r_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_19445__boxed_5970_ = crate::leanh::lean_unbox_usize(v_x_5968_);
    crate::leanh::lean_dec(v_x_5968_);
    v_res_5971_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_5967_, v_x_19445__boxed_5970_, v_x_5969_);
    crate::leanh::lean_dec_ref(v_x_5969_);
    crate::leanh::lean_dec_ref(v_x_5967_);
    v_r_5972_ = crate::leanh::lean_box((v_res_5971_) as usize);
    return v_r_5972_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(
    mut v_x_5973_: *mut crate::leanh::LeanObject,
    mut v_x_5974_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5975_: u64 = 0;
    let mut v___x_5976_: usize = 0;
    let mut v___x_5977_: u8 = 0;
    v___x_5975_ = l_Lean_instHashableExtraModUse_hash(v_x_5974_);
    v___x_5976_ = lean_uint64_to_usize(v___x_5975_);
    v___x_5977_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_5973_, v___x_5976_, v_x_5974_);
    return v___x_5977_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg___boxed(
    mut v_x_5978_: *mut crate::leanh::LeanObject,
    mut v_x_5979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5980_: u8 = 0;
    let mut v_r_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5980_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_5978_, v_x_5979_);
    crate::leanh::lean_dec_ref(v_x_5979_);
    crate::leanh::lean_dec_ref(v_x_5978_);
    v_r_5981_ = crate::leanh::lean_box((v_res_5980_) as usize);
    return v_r_5981_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0()
-> f64 {
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: f64 = 0.0;
    v___x_5982_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5983_ = lean_float_of_nat(v___x_5982_);
    return v___x_5983_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(
    mut v_cls_5987_: *mut crate::leanh::LeanObject,
    mut v_msg_5988_: *mut crate::leanh::LeanObject,
    mut v___y_5989_: *mut crate::leanh::LeanObject,
    mut v___y_5990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5998_: u8 = 0;
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6013_: u8 = 0;
    let mut v_tid_6014_: u64 = 0;
    let mut v_traces_6015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6018_: u8 = 0;
    let mut v___x_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: f64 = 0.0;
    let mut v___x_6021_: u8 = 0;
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6039_: u8 = 0;
    let mut v_isSharedCheck_6040_: u8 = 0;
    let mut v_isSharedCheck_6041_: u8 = 0;
    let mut v_a_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6045_: u8 = 0;
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5992_ = l_Lean_Elab_Command_getRef___redArg(v___y_5989_);
                if crate::leanh::lean_obj_tag(v___x_5992_) == 0 {
                    v_a_5993_ = crate::leanh::lean_ctor_get(v___x_5992_, 0);
                    crate::leanh::lean_inc(v_a_5993_);
                    crate::leanh::lean_dec_ref_known(v___x_5992_, 1);
                    v___x_5994_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_Command_elabElabRulesAux_spec__6_spec__6___redArg(v_msg_5988_, v___y_5990_);
                    v_a_5995_ = crate::leanh::lean_ctor_get(v___x_5994_, 0);
                    v_isSharedCheck_6041_ = (!crate::leanh::lean_is_exclusive(v___x_5994_)) as u8;
                    if v_isSharedCheck_6041_ == 0 {
                        v___x_5997_ = v___x_5994_;
                        v_isShared_5998_ = v_isSharedCheck_6041_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5995_);
                        crate::leanh::lean_dec(v___x_5994_);
                        v___x_5997_ = crate::leanh::lean_box(0);
                        v_isShared_5998_ = v_isSharedCheck_6041_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msg_5988_);
                    crate::leanh::lean_dec(v_cls_5987_);
                    v_a_6042_ = crate::leanh::lean_ctor_get(v___x_5992_, 0);
                    v_isSharedCheck_6049_ = (!crate::leanh::lean_is_exclusive(v___x_5992_)) as u8;
                    if v_isSharedCheck_6049_ == 0 {
                        v___x_6044_ = v___x_5992_;
                        v_isShared_6045_ = v_isSharedCheck_6049_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6042_);
                        crate::leanh::lean_dec(v___x_5992_);
                        v___x_6044_ = crate::leanh::lean_box(0);
                        v_isShared_6045_ = v_isSharedCheck_6049_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5999_ = lean_st_ref_take(v___y_5990_);
                v_traceState_6000_ = crate::leanh::lean_ctor_get(v___x_5999_, 9);
                v_env_6001_ = crate::leanh::lean_ctor_get(v___x_5999_, 0);
                v_messages_6002_ = crate::leanh::lean_ctor_get(v___x_5999_, 1);
                v_scopes_6003_ = crate::leanh::lean_ctor_get(v___x_5999_, 2);
                v_usedQuotCtxts_6004_ = crate::leanh::lean_ctor_get(v___x_5999_, 3);
                v_nextMacroScope_6005_ = crate::leanh::lean_ctor_get(v___x_5999_, 4);
                v_maxRecDepth_6006_ = crate::leanh::lean_ctor_get(v___x_5999_, 5);
                v_ngen_6007_ = crate::leanh::lean_ctor_get(v___x_5999_, 6);
                v_auxDeclNGen_6008_ = crate::leanh::lean_ctor_get(v___x_5999_, 7);
                v_infoState_6009_ = crate::leanh::lean_ctor_get(v___x_5999_, 8);
                v_snapshotTasks_6010_ = crate::leanh::lean_ctor_get(v___x_5999_, 10);
                v_isSharedCheck_6040_ = (!crate::leanh::lean_is_exclusive(v___x_5999_)) as u8;
                if v_isSharedCheck_6040_ == 0 {
                    v___x_6012_ = v___x_5999_;
                    v_isShared_6013_ = v_isSharedCheck_6040_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6010_);
                    crate::leanh::lean_inc(v_traceState_6000_);
                    crate::leanh::lean_inc(v_infoState_6009_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6008_);
                    crate::leanh::lean_inc(v_ngen_6007_);
                    crate::leanh::lean_inc(v_maxRecDepth_6006_);
                    crate::leanh::lean_inc(v_nextMacroScope_6005_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_6004_);
                    crate::leanh::lean_inc(v_scopes_6003_);
                    crate::leanh::lean_inc(v_messages_6002_);
                    crate::leanh::lean_inc(v_env_6001_);
                    crate::leanh::lean_dec(v___x_5999_);
                    v___x_6012_ = crate::leanh::lean_box(0);
                    v_isShared_6013_ = v_isSharedCheck_6040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6014_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_6000_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6015_ = crate::leanh::lean_ctor_get(v_traceState_6000_, 0);
                v_isSharedCheck_6039_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_6000_)) as u8;
                if v_isSharedCheck_6039_ == 0 {
                    v___x_6017_ = v_traceState_6000_;
                    v_isShared_6018_ = v_isSharedCheck_6039_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_6015_);
                    crate::leanh::lean_dec(v_traceState_6000_);
                    v___x_6017_ = crate::leanh::lean_box(0);
                    v_isShared_6018_ = v_isSharedCheck_6039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6019_ = crate::leanh::lean_box(0);
                v___x_6020_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__0);
                v___x_6021_ = 0;
                v___x_6022_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1;
                v___x_6023_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_6023_, 0, v_cls_5987_);
                crate::leanh::lean_ctor_set(v___x_6023_, 1, v___x_6019_);
                crate::leanh::lean_ctor_set(v___x_6023_, 2, v___x_6022_);
                crate::leanh::lean_ctor_set_float(
                    v___x_6023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_6020_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_6023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6020_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6023_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6021_,
                );
                v___x_6024_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__2;
                v___x_6025_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6025_, 0, v___x_6023_);
                crate::leanh::lean_ctor_set(v___x_6025_, 1, v_a_5995_);
                crate::leanh::lean_ctor_set(v___x_6025_, 2, v___x_6024_);
                v___x_6026_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6026_, 0, v_a_5993_);
                crate::leanh::lean_ctor_set(v___x_6026_, 1, v___x_6025_);
                v___x_6027_ = l_Lean_PersistentArray_push___redArg(v_traces_6015_, v___x_6026_);
                if v_isShared_6018_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6017_, 0, v___x_6027_);
                    v___x_6029_ = v___x_6017_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6038_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6038_, 0, v___x_6027_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6038_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_6014_,
                    );
                    v___x_6029_ = v_reuseFailAlloc_6038_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6012_, 9, v___x_6029_);
                    v___x_6031_ = v___x_6012_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6037_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 0, v_env_6001_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 1, v_messages_6002_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 2, v_scopes_6003_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 3, v_usedQuotCtxts_6004_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 4, v_nextMacroScope_6005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 5, v_maxRecDepth_6006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 6, v_ngen_6007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 7, v_auxDeclNGen_6008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 8, v_infoState_6009_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 9, v___x_6029_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6037_, 10, v_snapshotTasks_6010_);
                    v___x_6031_ = v_reuseFailAlloc_6037_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6032_ = lean_st_ref_set(v___y_5990_, v___x_6031_);
                v___x_6033_ = crate::leanh::lean_box(0);
                if v_isShared_5998_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5997_, 0, v___x_6033_);
                    v___x_6035_ = v___x_5997_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_6033_);
                    v___x_6035_ = v_reuseFailAlloc_6036_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6035_;
            }
            7 => {
                if v_isShared_6045_ == 0 {
                    v___x_6047_ = v___x_6044_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6048_, 0, v_a_6042_);
                    v___x_6047_ = v_reuseFailAlloc_6048_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___boxed(
    mut v_cls_6050_: *mut crate::leanh::LeanObject,
    mut v_msg_6051_: *mut crate::leanh::LeanObject,
    mut v___y_6052_: *mut crate::leanh::LeanObject,
    mut v___y_6053_: *mut crate::leanh::LeanObject,
    mut v___y_6054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6055_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_6050_, v_msg_6051_, v___y_6052_, v___y_6053_);
    crate::leanh::lean_dec(v___y_6053_);
    crate::leanh::lean_dec_ref(v___y_6052_);
    return v_res_6055_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6058_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__1;
    v___x_6059_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__0;
    v___x_6060_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6059_,
        v___x_6058_,
    );
    return v___x_6060_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6065_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__5;
    v___x_6066_ = l_Lean_stringToMessageData(v___x_6065_);
    return v___x_6066_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6068_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__7;
    v___x_6069_ = l_Lean_stringToMessageData(v___x_6068_);
    return v___x_6069_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6070_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0___closed__1;
    v___x_6071_ = l_Lean_stringToMessageData(v___x_6070_);
    return v___x_6071_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_6075_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4;
    v___x_6076_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11;
    v___x_6077_ = l_Lean_Name_append(v___x_6076_, v_cls_6075_);
    return v___x_6077_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6079_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__13;
    v___x_6080_ = l_Lean_stringToMessageData(v___x_6079_);
    return v___x_6080_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6082_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__15;
    v___x_6083_ = l_Lean_stringToMessageData(v___x_6082_);
    return v___x_6083_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(
    mut v_mod_6088_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6089_: u8,
    mut v_hint_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
    mut v___y_6092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_6096_: u8 = 0;
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v_asyncMode_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6130_: u8 = 0;
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6132_: u8 = 0;
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6140_: u8 = 0;
    let mut v_cls_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6162_: u8 = 0;
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6094_ = lean_st_ref_get(v___y_6092_);
                v_env_6095_ = crate::leanh::lean_ctor_get(v___x_6094_, 0);
                crate::leanh::lean_inc_ref(v_env_6095_);
                crate::leanh::lean_dec(v___x_6094_);
                v_isExporting_6096_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_6095_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_6095_);
                v___x_6097_ = lean_st_ref_get(v___y_6092_);
                v_env_6098_ = crate::leanh::lean_ctor_get(v___x_6097_, 0);
                crate::leanh::lean_inc_ref(v_env_6098_);
                crate::leanh::lean_dec(v___x_6097_);
                v___x_6099_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__2);
                crate::leanh::lean_inc(v_mod_6088_);
                v_entry_6100_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_6100_, 0, v_mod_6088_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_6100_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_6096_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_6100_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_6089_,
                );
                v___x_6101_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_6102_ = crate::leanh::lean_box(1);
                v___x_6103_ = crate::leanh::lean_box(0);
                v___x_6131_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_6099_,
                    v___x_6101_,
                    v_env_6098_,
                    v___x_6102_,
                    v___x_6103_,
                );
                v___x_6132_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v___x_6131_, v_entry_6100_);
                crate::leanh::lean_dec(v___x_6131_);
                if v___x_6132_ == 0 {
                    v___x_6133_ = l_Lean_inheritedTraceOptions;
                    v___x_6134_ = lean_st_ref_get(v___x_6133_);
                    v___x_6135_ = lean_st_ref_get(v___y_6092_);
                    v_scopes_6136_ = crate::leanh::lean_ctor_get(v___x_6135_, 2);
                    crate::leanh::lean_inc(v_scopes_6136_);
                    crate::leanh::lean_dec(v___x_6135_);
                    v___x_6137_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_6138_ = l_List_head_x21___redArg(v___x_6137_, v_scopes_6136_);
                    crate::leanh::lean_dec(v_scopes_6136_);
                    v_opts_6139_ = crate::leanh::lean_ctor_get(v___x_6138_, 1);
                    crate::leanh::lean_inc_ref(v_opts_6139_);
                    crate::leanh::lean_dec(v___x_6138_);
                    v_hasTrace_6140_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_6139_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6140_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_6139_);
                        crate::leanh::lean_dec(v___x_6134_);
                        crate::leanh::lean_dec(v_hint_6090_);
                        crate::leanh::lean_dec(v_mod_6088_);
                        v___y_6105_ = v___y_6092_;
                        state = 1;
                        continue;
                    } else {
                        v_cls_6141_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__4;
                        v___x_6161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__12);
                        v___x_6162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_6134_,
                            v_opts_6139_,
                            v___x_6161_,
                        );
                        crate::leanh::lean_dec_ref(v_opts_6139_);
                        crate::leanh::lean_dec(v___x_6134_);
                        if v___x_6162_ == 0 {
                            crate::leanh::lean_dec(v_hint_6090_);
                            crate::leanh::lean_dec(v_mod_6088_);
                            v___y_6105_ = v___y_6092_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6163_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__14);
                            if v_isExporting_6096_ == 0 {
                                v___x_6172_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__19;
                                v___y_6165_ = v___x_6172_;
                                state = 6;
                                continue;
                            } else {
                                v___x_6173_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__20;
                                v___y_6165_ = v___x_6173_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_6100_, 1);
                    crate::leanh::lean_dec(v_hint_6090_);
                    crate::leanh::lean_dec(v_mod_6088_);
                    v___x_6174_ = crate::leanh::lean_box(0);
                    v___x_6175_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6175_, 0, v___x_6174_);
                    return v___x_6175_;
                }
            }
            1 => {
                v___x_6106_ = lean_st_ref_take(v___y_6105_);
                v_toEnvExtension_6107_ = crate::leanh::lean_ctor_get(v___x_6101_, 0);
                v_env_6108_ = crate::leanh::lean_ctor_get(v___x_6106_, 0);
                v_messages_6109_ = crate::leanh::lean_ctor_get(v___x_6106_, 1);
                v_scopes_6110_ = crate::leanh::lean_ctor_get(v___x_6106_, 2);
                v_usedQuotCtxts_6111_ = crate::leanh::lean_ctor_get(v___x_6106_, 3);
                v_nextMacroScope_6112_ = crate::leanh::lean_ctor_get(v___x_6106_, 4);
                v_maxRecDepth_6113_ = crate::leanh::lean_ctor_get(v___x_6106_, 5);
                v_ngen_6114_ = crate::leanh::lean_ctor_get(v___x_6106_, 6);
                v_auxDeclNGen_6115_ = crate::leanh::lean_ctor_get(v___x_6106_, 7);
                v_infoState_6116_ = crate::leanh::lean_ctor_get(v___x_6106_, 8);
                v_traceState_6117_ = crate::leanh::lean_ctor_get(v___x_6106_, 9);
                v_snapshotTasks_6118_ = crate::leanh::lean_ctor_get(v___x_6106_, 10);
                v_isSharedCheck_6130_ = (!crate::leanh::lean_is_exclusive(v___x_6106_)) as u8;
                if v_isSharedCheck_6130_ == 0 {
                    v___x_6120_ = v___x_6106_;
                    v_isShared_6121_ = v_isSharedCheck_6130_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6118_);
                    crate::leanh::lean_inc(v_traceState_6117_);
                    crate::leanh::lean_inc(v_infoState_6116_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6115_);
                    crate::leanh::lean_inc(v_ngen_6114_);
                    crate::leanh::lean_inc(v_maxRecDepth_6113_);
                    crate::leanh::lean_inc(v_nextMacroScope_6112_);
                    crate::leanh::lean_inc(v_usedQuotCtxts_6111_);
                    crate::leanh::lean_inc(v_scopes_6110_);
                    crate::leanh::lean_inc(v_messages_6109_);
                    crate::leanh::lean_inc(v_env_6108_);
                    crate::leanh::lean_dec(v___x_6106_);
                    v___x_6120_ = crate::leanh::lean_box(0);
                    v_isShared_6121_ = v_isSharedCheck_6130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_6122_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6107_, 2);
                v___x_6123_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_6101_,
                    v_env_6108_,
                    v_entry_6100_,
                    v_asyncMode_6122_,
                    v___x_6103_,
                );
                if v_isShared_6121_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6120_, 0, v___x_6123_);
                    v___x_6125_ = v___x_6120_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6129_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 0, v___x_6123_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 1, v_messages_6109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 2, v_scopes_6110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 3, v_usedQuotCtxts_6111_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 4, v_nextMacroScope_6112_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 5, v_maxRecDepth_6113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 6, v_ngen_6114_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 7, v_auxDeclNGen_6115_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 8, v_infoState_6116_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 9, v_traceState_6117_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6129_, 10, v_snapshotTasks_6118_);
                    v___x_6125_ = v_reuseFailAlloc_6129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6126_ = lean_st_ref_set(v___y_6105_, v___x_6125_);
                v___x_6127_ = crate::leanh::lean_box(0);
                v___x_6128_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6128_, 0, v___x_6127_);
                return v___x_6128_;
            }
            4 => {
                v___x_6145_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6145_, 0, v___y_6143_);
                crate::leanh::lean_ctor_set(v___x_6145_, 1, v___y_6144_);
                v___x_6146_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_cls_6141_, v___x_6145_, v___y_6091_, v___y_6092_);
                if crate::leanh::lean_obj_tag(v___x_6146_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6146_, 1);
                    v___y_6105_ = v___y_6092_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_6100_, 1);
                    return v___x_6146_;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref(v___y_6149_);
                v___x_6150_ = l_Lean_stringToMessageData(v___y_6149_);
                v___x_6151_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6151_, 0, v___y_6148_);
                crate::leanh::lean_ctor_set(v___x_6151_, 1, v___x_6150_);
                v___x_6152_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__6);
                v___x_6153_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6153_, 0, v___x_6151_);
                crate::leanh::lean_ctor_set(v___x_6153_, 1, v___x_6152_);
                v___x_6154_ = l_Lean_MessageData_ofName(v_mod_6088_);
                v___x_6155_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6155_, 0, v___x_6153_);
                crate::leanh::lean_ctor_set(v___x_6155_, 1, v___x_6154_);
                v___x_6156_ = l_Lean_Name_isAnonymous(v_hint_6090_);
                if v___x_6156_ == 0 {
                    v___x_6157_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__8);
                    v___x_6158_ = l_Lean_MessageData_ofName(v_hint_6090_);
                    v___x_6159_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6159_, 0, v___x_6157_);
                    crate::leanh::lean_ctor_set(v___x_6159_, 1, v___x_6158_);
                    v___y_6143_ = v___x_6155_;
                    v___y_6144_ = v___x_6159_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_6090_);
                    v___x_6160_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__9);
                    v___y_6143_ = v___x_6155_;
                    v___y_6144_ = v___x_6160_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc_ref(v___y_6165_);
                v___x_6166_ = l_Lean_stringToMessageData(v___y_6165_);
                v___x_6167_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6167_, 0, v___x_6163_);
                crate::leanh::lean_ctor_set(v___x_6167_, 1, v___x_6166_);
                v___x_6168_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__16);
                v___x_6169_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6169_, 0, v___x_6167_);
                crate::leanh::lean_ctor_set(v___x_6169_, 1, v___x_6168_);
                if v_isMeta_6089_ == 0 {
                    v___x_6170_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__17;
                    v___y_6148_ = v___x_6169_;
                    v___y_6149_ = v___x_6170_;
                    state = 5;
                    continue;
                } else {
                    v___x_6171_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__18;
                    v___y_6148_ = v___x_6169_;
                    v___y_6149_ = v___x_6171_;
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___boxed(
    mut v_mod_6176_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6177_: *mut crate::leanh::LeanObject,
    mut v_hint_6178_: *mut crate::leanh::LeanObject,
    mut v___y_6179_: *mut crate::leanh::LeanObject,
    mut v___y_6180_: *mut crate::leanh::LeanObject,
    mut v___y_6181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6182_: u8 = 0;
    let mut v_res_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6182_ = (crate::leanh::lean_unbox(v_isMeta_6177_) as u8);
    v_res_6183_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_mod_6176_, v_isMeta_boxed_6182_, v_hint_6178_, v___y_6179_, v___y_6180_);
    crate::leanh::lean_dec(v___y_6180_);
    crate::leanh::lean_dec_ref(v___y_6179_);
    return v_res_6183_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(
    mut v___x_6184_: *mut crate::leanh::LeanObject,
    mut v_declName_6185_: *mut crate::leanh::LeanObject,
    mut v_as_6186_: *mut crate::leanh::LeanObject,
    mut v_sz_6187_: usize,
    mut v_i_6188_: usize,
    mut v_b_6189_: *mut crate::leanh::LeanObject,
    mut v___y_6190_: *mut crate::leanh::LeanObject,
    mut v___y_6191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6193_: u8 = 0;
    let mut v___x_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6202_: u8 = 0;
    let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: usize = 0;
    let mut v___x_6206_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6193_ = lean_usize_dec_lt(v_i_6188_, v_sz_6187_);
                if v___x_6193_ == 0 {
                    crate::leanh::lean_dec(v_declName_6185_);
                    v___x_6194_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6194_, 0, v_b_6189_);
                    return v___x_6194_;
                } else {
                    v___x_6195_ = l_Lean_Environment_header(v___x_6184_);
                    v_modules_6196_ = crate::leanh::lean_ctor_get(v___x_6195_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6196_);
                    crate::leanh::lean_dec_ref(v___x_6195_);
                    v___x_6197_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_6198_ = lean_array_uget_borrowed(v_as_6186_, v_i_6188_);
                    v___x_6199_ = lean_array_get(v___x_6197_, v_modules_6196_, v_a_6198_);
                    crate::leanh::lean_dec_ref(v_modules_6196_);
                    v_toImport_6200_ = crate::leanh::lean_ctor_get(v___x_6199_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_6200_);
                    crate::leanh::lean_dec(v___x_6199_);
                    v_module_6201_ = crate::leanh::lean_ctor_get(v_toImport_6200_, 0);
                    crate::leanh::lean_inc(v_module_6201_);
                    crate::leanh::lean_dec_ref(v_toImport_6200_);
                    v___x_6202_ = 0;
                    crate::leanh::lean_inc(v_declName_6185_);
                    v___x_6203_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_6201_, v___x_6202_, v_declName_6185_, v___y_6190_, v___y_6191_);
                    if crate::leanh::lean_obj_tag(v___x_6203_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6203_, 1);
                        v___x_6204_ = crate::leanh::lean_box(0);
                        v___x_6205_ = 1usize;
                        v___x_6206_ = lean_usize_add(v_i_6188_, v___x_6205_);
                        v_i_6188_ = v___x_6206_;
                        v_b_6189_ = v___x_6204_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_6185_);
                        return v___x_6203_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4___boxed(
    mut v___x_6208_: *mut crate::leanh::LeanObject,
    mut v_declName_6209_: *mut crate::leanh::LeanObject,
    mut v_as_6210_: *mut crate::leanh::LeanObject,
    mut v_sz_6211_: *mut crate::leanh::LeanObject,
    mut v_i_6212_: *mut crate::leanh::LeanObject,
    mut v_b_6213_: *mut crate::leanh::LeanObject,
    mut v___y_6214_: *mut crate::leanh::LeanObject,
    mut v___y_6215_: *mut crate::leanh::LeanObject,
    mut v___y_6216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6217_: usize = 0;
    let mut v_i_boxed_6218_: usize = 0;
    let mut v_res_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6217_ = crate::leanh::lean_unbox_usize(v_sz_6211_);
    crate::leanh::lean_dec(v_sz_6211_);
    v_i_boxed_6218_ = crate::leanh::lean_unbox_usize(v_i_6212_);
    crate::leanh::lean_dec(v_i_6212_);
    v_res_6219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v___x_6208_, v_declName_6209_, v_as_6210_, v_sz_boxed_6217_, v_i_boxed_6218_, v_b_6213_, v___y_6214_, v___y_6215_);
    crate::leanh::lean_dec(v___y_6215_);
    crate::leanh::lean_dec_ref(v___y_6214_);
    crate::leanh::lean_dec_ref(v_as_6210_);
    crate::leanh::lean_dec_ref(v___x_6208_);
    return v_res_6219_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(
    mut v_a_6220_: *mut crate::leanh::LeanObject,
    mut v_x_6221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: u8 = 0;
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6221_) == 0 {
                    v___x_6222_ = crate::leanh::lean_box(0);
                    return v___x_6222_;
                } else {
                    v_key_6223_ = crate::leanh::lean_ctor_get(v_x_6221_, 0);
                    v_value_6224_ = crate::leanh::lean_ctor_get(v_x_6221_, 1);
                    v_tail_6225_ = crate::leanh::lean_ctor_get(v_x_6221_, 2);
                    v___x_6226_ = lean_name_eq(v_key_6223_, v_a_6220_);
                    if v___x_6226_ == 0 {
                        v_x_6221_ = v_tail_6225_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_6224_);
                        v___x_6228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6228_, 0, v_value_6224_);
                        return v___x_6228_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg___boxed(
    mut v_a_6229_: *mut crate::leanh::LeanObject,
    mut v_x_6230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6231_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_6229_, v_x_6230_);
    crate::leanh::lean_dec(v_x_6230_);
    crate::leanh::lean_dec(v_a_6229_);
    return v_res_6231_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0()
-> u64 {
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: u64 = 0;
    v___x_6232_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_6233_ = lean_uint64_of_nat(v___x_6232_);
    return v___x_6233_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(
    mut v_m_6234_: *mut crate::leanh::LeanObject,
    mut v_a_6235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_6236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6239_: u64 = 0;
    let mut v___x_6240_: u64 = 0;
    let mut v___x_6241_: u64 = 0;
    let mut v_fold_6242_: u64 = 0;
    let mut v___x_6243_: u64 = 0;
    let mut v___x_6244_: u64 = 0;
    let mut v___x_6245_: u64 = 0;
    let mut v___x_6246_: usize = 0;
    let mut v___x_6247_: usize = 0;
    let mut v___x_6248_: usize = 0;
    let mut v___x_6249_: usize = 0;
    let mut v___x_6250_: usize = 0;
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: u64 = 0;
    let mut v_hash_6254_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_6236_ = crate::leanh::lean_ctor_get(v_m_6234_, 1);
                v___x_6237_ = lean_array_get_size(v_buckets_6236_);
                if crate::leanh::lean_obj_tag(v_a_6235_) == 0 {
                    v___x_6253_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___closed__0);
                    v___y_6239_ = v___x_6253_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6254_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_6235_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_6239_ = v_hash_6254_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6240_ = 32u64;
                v___x_6241_ = lean_uint64_shift_right(v___y_6239_, v___x_6240_);
                v_fold_6242_ = lean_uint64_xor(v___y_6239_, v___x_6241_);
                v___x_6243_ = 16u64;
                v___x_6244_ = lean_uint64_shift_right(v_fold_6242_, v___x_6243_);
                v___x_6245_ = lean_uint64_xor(v_fold_6242_, v___x_6244_);
                v___x_6246_ = lean_uint64_to_usize(v___x_6245_);
                v___x_6247_ = lean_usize_of_nat(v___x_6237_);
                v___x_6248_ = 1usize;
                v___x_6249_ = lean_usize_sub(v___x_6247_, v___x_6248_);
                v___x_6250_ = lean_usize_land(v___x_6246_, v___x_6249_);
                v___x_6251_ = lean_array_uget_borrowed(v_buckets_6236_, v___x_6250_);
                v___x_6252_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_6235_, v___x_6251_);
                return v___x_6252_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_m_6255_: *mut crate::leanh::LeanObject,
    mut v_a_6256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6257_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_6255_, v_a_6256_);
    crate::leanh::lean_dec(v_a_6256_);
    crate::leanh::lean_dec_ref(v_m_6255_);
    return v_res_6257_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6260_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__1;
    v___x_6261_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__0;
    v___x_6262_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_6261_,
        v___x_6260_,
    );
    return v___x_6262_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(
    mut v_declName_6265_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6266_: u8,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6278_: usize = 0;
    let mut v___x_6279_: usize = 0;
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6287_: u8 = 0;
    let mut v_unused_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: u8 = 0;
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6300_: u8 = 0;
    let mut v_toImport_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: u8 = 0;
    let mut v___x_6312_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6270_ = lean_st_ref_get(v___y_6268_);
                v_env_6274_ = crate::leanh::lean_ctor_get(v___x_6270_, 0);
                crate::leanh::lean_inc_ref(v_env_6274_);
                crate::leanh::lean_dec(v___x_6270_);
                v___x_6289_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6274_, v_declName_6265_);
                if crate::leanh::lean_obj_tag(v___x_6289_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_6274_);
                    crate::leanh::lean_dec(v_declName_6265_);
                    state = 1;
                    continue;
                } else {
                    v_val_6290_ = crate::leanh::lean_ctor_get(v___x_6289_, 0);
                    crate::leanh::lean_inc(v_val_6290_);
                    crate::leanh::lean_dec_ref_known(v___x_6289_, 1);
                    v___x_6291_ = l_Lean_Environment_header(v_env_6274_);
                    v_modules_6292_ = crate::leanh::lean_ctor_get(v___x_6291_, 3);
                    crate::leanh::lean_inc_ref(v_modules_6292_);
                    crate::leanh::lean_dec_ref(v___x_6291_);
                    v___x_6293_ = lean_array_get_size(v_modules_6292_);
                    v___x_6294_ = lean_nat_dec_lt(v_val_6290_, v___x_6293_);
                    if v___x_6294_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_6292_);
                        crate::leanh::lean_dec(v_val_6290_);
                        crate::leanh::lean_dec_ref(v_env_6274_);
                        crate::leanh::lean_dec(v_declName_6265_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6295_ = lean_st_ref_get(v___y_6268_);
                        v_env_6296_ = crate::leanh::lean_ctor_get(v___x_6295_, 0);
                        crate::leanh::lean_inc_ref(v_env_6296_);
                        crate::leanh::lean_dec(v___x_6295_);
                        v___x_6297_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__2);
                        v___x_6298_ = lean_array_fget(v_modules_6292_, v_val_6290_);
                        crate::leanh::lean_dec(v_val_6290_);
                        crate::leanh::lean_dec_ref(v_modules_6292_);
                        if v_isMeta_6266_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_6296_);
                            v___y_6300_ = v_isMeta_6266_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_6265_);
                            v___x_6311_ = l_Lean_isMarkedMeta(v_env_6296_, v_declName_6265_);
                            if v___x_6311_ == 0 {
                                v___y_6300_ = v_isMeta_6266_;
                                state = 5;
                                continue;
                            } else {
                                v___x_6312_ = 0;
                                v___y_6300_ = v___x_6312_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6272_ = crate::leanh::lean_box(0);
                v___x_6273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6273_, 0, v___x_6272_);
                return v___x_6273_;
            }
            2 => {
                v___x_6277_ = crate::leanh::lean_box(0);
                v_sz_6278_ = lean_array_size(v___y_6276_);
                v___x_6279_ = 0usize;
                v___x_6280_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__4(v_env_6274_, v_declName_6265_, v___y_6276_, v_sz_6278_, v___x_6279_, v___x_6277_, v___y_6267_, v___y_6268_);
                crate::leanh::lean_dec_ref(v___y_6276_);
                crate::leanh::lean_dec_ref(v_env_6274_);
                if crate::leanh::lean_obj_tag(v___x_6280_) == 0 {
                    v_isSharedCheck_6287_ = (!crate::leanh::lean_is_exclusive(v___x_6280_)) as u8;
                    if v_isSharedCheck_6287_ == 0 {
                        v_unused_6288_ = crate::leanh::lean_ctor_get(v___x_6280_, 0);
                        crate::leanh::lean_dec(v_unused_6288_);
                        v___x_6282_ = v___x_6280_;
                        v_isShared_6283_ = v_isSharedCheck_6287_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6280_);
                        v___x_6282_ = crate::leanh::lean_box(0);
                        v_isShared_6283_ = v_isSharedCheck_6287_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_6280_;
                }
            }
            3 => {
                if v_isShared_6283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6282_, 0, v___x_6277_);
                    v___x_6285_ = v___x_6282_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6286_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6286_, 0, v___x_6277_);
                    v___x_6285_ = v_reuseFailAlloc_6286_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6285_;
            }
            5 => {
                v_toImport_6301_ = crate::leanh::lean_ctor_get(v___x_6298_, 0);
                crate::leanh::lean_inc_ref(v_toImport_6301_);
                crate::leanh::lean_dec(v___x_6298_);
                v_module_6302_ = crate::leanh::lean_ctor_get(v_toImport_6301_, 0);
                crate::leanh::lean_inc(v_module_6302_);
                crate::leanh::lean_dec_ref(v_toImport_6301_);
                crate::leanh::lean_inc(v_declName_6265_);
                v___x_6303_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3(v_module_6302_, v___y_6300_, v_declName_6265_, v___y_6267_, v___y_6268_);
                if crate::leanh::lean_obj_tag(v___x_6303_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6303_, 1);
                    v___x_6304_ = l_Lean_indirectModUseExt;
                    v___x_6305_ = crate::leanh::lean_box(1);
                    v___x_6306_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_6274_);
                    v___x_6307_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_6297_,
                        v___x_6304_,
                        v_env_6274_,
                        v___x_6305_,
                        v___x_6306_,
                    );
                    v___x_6308_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v___x_6307_, v_declName_6265_);
                    crate::leanh::lean_dec(v___x_6307_);
                    if crate::leanh::lean_obj_tag(v___x_6308_) == 0 {
                        v___x_6309_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___closed__3;
                        v___y_6276_ = v___x_6309_;
                        state = 2;
                        continue;
                    } else {
                        v_val_6310_ = crate::leanh::lean_ctor_get(v___x_6308_, 0);
                        crate::leanh::lean_inc(v_val_6310_);
                        crate::leanh::lean_dec_ref_known(v___x_6308_, 1);
                        v___y_6276_ = v_val_6310_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_6274_);
                    crate::leanh::lean_dec(v_declName_6265_);
                    return v___x_6303_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2___boxed(
    mut v_declName_6313_: *mut crate::leanh::LeanObject,
    mut v_isMeta_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
    mut v___y_6316_: *mut crate::leanh::LeanObject,
    mut v___y_6317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_6318_: u8 = 0;
    let mut v_res_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_6318_ = (crate::leanh::lean_unbox(v_isMeta_6314_) as u8);
    v_res_6319_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_declName_6313_, v_isMeta_boxed_6318_, v___y_6315_, v___y_6316_);
    crate::leanh::lean_dec(v___y_6316_);
    crate::leanh::lean_dec_ref(v___y_6315_);
    return v_res_6319_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(
    mut v_as_x27_6320_: *mut crate::leanh::LeanObject,
    mut v_b_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: u8 = 0;
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_6320_) == 0 {
                    v___x_6325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6325_, 0, v_b_6321_);
                    return v___x_6325_;
                } else {
                    v_head_6326_ = crate::leanh::lean_ctor_get(v_as_x27_6320_, 0);
                    v_tail_6327_ = crate::leanh::lean_ctor_get(v_as_x27_6320_, 1);
                    v___x_6328_ = 1;
                    crate::leanh::lean_inc(v_head_6326_);
                    v___x_6329_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2(v_head_6326_, v___x_6328_, v___y_6322_, v___y_6323_);
                    if crate::leanh::lean_obj_tag(v___x_6329_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6329_, 1);
                        v___x_6330_ = crate::leanh::lean_box(0);
                        v_as_x27_6320_ = v_tail_6327_;
                        v_b_6321_ = v___x_6330_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6329_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg___boxed(
    mut v_as_x27_6332_: *mut crate::leanh::LeanObject,
    mut v_b_6333_: *mut crate::leanh::LeanObject,
    mut v___y_6334_: *mut crate::leanh::LeanObject,
    mut v___y_6335_: *mut crate::leanh::LeanObject,
    mut v___y_6336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6337_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_6332_, v_b_6333_, v___y_6334_, v___y_6335_);
    crate::leanh::lean_dec(v___y_6335_);
    crate::leanh::lean_dec_ref(v___y_6334_);
    crate::leanh::lean_dec(v_as_x27_6332_);
    return v_res_6337_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6343_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6344_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6344_, 0, v___x_6343_);
    return v___x_6344_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6345_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__3);
    v___x_6346_ = l_Lean_MessageData_ofFormat(v___x_6345_);
    return v___x_6346_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6347_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__4);
    v___x_6348_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__2;
    v___x_6349_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6349_, 0, v___x_6348_);
    crate::leanh::lean_ctor_set(v___x_6349_, 1, v___x_6347_);
    return v___x_6349_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(
    mut v_ref_6350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6352_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___closed__5);
    v___x_6353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6353_, 0, v_ref_6350_);
    crate::leanh::lean_ctor_set(v___x_6353_, 1, v___x_6352_);
    v___x_6354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6354_, 0, v___x_6353_);
    return v___x_6354_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg___boxed(
    mut v_ref_6355_: *mut crate::leanh::LeanObject,
    mut v___y_6356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6357_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_6355_);
    return v_res_6357_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(
    mut v_currNamespace_6358_: *mut crate::leanh::LeanObject,
    mut v___y_6359_: *mut crate::leanh::LeanObject,
    mut v___y_6360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6361_, 0, v_currNamespace_6358_);
    crate::leanh::lean_ctor_set(v___x_6361_, 1, v___y_6360_);
    return v___x_6361_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed(
    mut v_currNamespace_6362_: *mut crate::leanh::LeanObject,
    mut v___y_6363_: *mut crate::leanh::LeanObject,
    mut v___y_6364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6365_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2(
            v_currNamespace_6362_,
            v___y_6363_,
            v___y_6364_,
        );
    crate::leanh::lean_dec_ref(v___y_6363_);
    return v_res_6365_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(
    mut v_env_6366_: *mut crate::leanh::LeanObject,
    mut v_declName_6367_: *mut crate::leanh::LeanObject,
    mut v___y_6368_: *mut crate::leanh::LeanObject,
    mut v___y_6369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6370_: u8 = 0;
    let mut v_env_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: u8 = 0;
    let mut v___x_6374_: u8 = 0;
    v___x_6370_ = 0;
    v_env_6371_ = l_Lean_Environment_setExporting(v_env_6366_, v___x_6370_);
    crate::leanh::lean_inc(v_declName_6367_);
    v___x_6372_ = l_Lean_mkPrivateName(v_env_6371_, v_declName_6367_);
    v___x_6373_ = 1;
    crate::leanh::lean_inc_ref(v_env_6371_);
    v___x_6374_ = l_Lean_Environment_contains(v_env_6371_, v___x_6372_, v___x_6373_);
    if v___x_6374_ == 0 {
        let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6376_: u8 = 0;
        let mut v___x_6377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6375_ = l_Lean_privateToUserName(v_declName_6367_);
        v___x_6376_ = l_Lean_Environment_contains(v_env_6371_, v___x_6375_, v___x_6373_);
        v___x_6377_ = crate::leanh::lean_box((v___x_6376_) as usize);
        v___x_6378_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6378_, 0, v___x_6377_);
        crate::leanh::lean_ctor_set(v___x_6378_, 1, v___y_6369_);
        return v___x_6378_;
    } else {
        let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_6371_);
        crate::leanh::lean_dec(v_declName_6367_);
        v___x_6379_ = crate::leanh::lean_box((v___x_6374_) as usize);
        v___x_6380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6380_, 0, v___x_6379_);
        crate::leanh::lean_ctor_set(v___x_6380_, 1, v___y_6369_);
        return v___x_6380_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed(
    mut v_env_6381_: *mut crate::leanh::LeanObject,
    mut v_declName_6382_: *mut crate::leanh::LeanObject,
    mut v___y_6383_: *mut crate::leanh::LeanObject,
    mut v___y_6384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6385_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0(
            v_env_6381_,
            v_declName_6382_,
            v___y_6383_,
            v___y_6384_,
        );
    crate::leanh::lean_dec_ref(v___y_6383_);
    return v_res_6385_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(
    mut v_x_6386_: *mut crate::leanh::LeanObject,
    mut v___y_6387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_6386_) == 0 {
        let mut v_a_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6388_ = crate::leanh::lean_ctor_get(v_x_6386_, 0);
        crate::leanh::lean_inc(v_a_6388_);
        v___x_6389_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6389_, 0, v_a_6388_);
        crate::leanh::lean_ctor_set(v___x_6389_, 1, v___y_6387_);
        return v___x_6389_;
    } else {
        let mut v_a_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_6390_ = crate::leanh::lean_ctor_get(v_x_6386_, 0);
        crate::leanh::lean_inc(v_a_6390_);
        v___x_6391_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_6391_, 0, v_a_6390_);
        crate::leanh::lean_ctor_set(v___x_6391_, 1, v___y_6387_);
        return v___x_6391_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg___boxed(
    mut v_x_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_6392_, v___y_6393_);
    crate::leanh::lean_dec_ref(v_x_6392_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(
    mut v_env_6395_: *mut crate::leanh::LeanObject,
    mut v_stx_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6404_: u8 = 0;
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6409_: u8 = 0;
    let mut v_unused_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v_snd_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6420_: u8 = 0;
    let mut v___x_6422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6425_: u8 = 0;
    let mut v_a_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6430_: u8 = 0;
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6438_: u8 = 0;
    let mut v_isSharedCheck_6439_: u8 = 0;
    let mut v_a_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6444_: u8 = 0;
    let mut v___x_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6399_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_6395_,
                    v_stx_6396_,
                    v___y_6397_,
                    v___y_6398_,
                );
                if crate::leanh::lean_obj_tag(v___x_6399_) == 0 {
                    v_a_6400_ = crate::leanh::lean_ctor_get(v___x_6399_, 0);
                    crate::leanh::lean_inc(v_a_6400_);
                    if crate::leanh::lean_obj_tag(v_a_6400_) == 0 {
                        v_a_6401_ = crate::leanh::lean_ctor_get(v___x_6399_, 1);
                        v_isSharedCheck_6409_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6399_)) as u8;
                        if v_isSharedCheck_6409_ == 0 {
                            v_unused_6410_ = crate::leanh::lean_ctor_get(v___x_6399_, 0);
                            crate::leanh::lean_dec(v_unused_6410_);
                            v___x_6403_ = v___x_6399_;
                            v_isShared_6404_ = v_isSharedCheck_6409_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6401_);
                            crate::leanh::lean_dec(v___x_6399_);
                            v___x_6403_ = crate::leanh::lean_box(0);
                            v_isShared_6404_ = v_isSharedCheck_6409_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_6411_ = crate::leanh::lean_ctor_get(v_a_6400_, 0);
                        v_isSharedCheck_6439_ = (!crate::leanh::lean_is_exclusive(v_a_6400_)) as u8;
                        if v_isSharedCheck_6439_ == 0 {
                            v___x_6413_ = v_a_6400_;
                            v_isShared_6414_ = v_isSharedCheck_6439_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6411_);
                            crate::leanh::lean_dec(v_a_6400_);
                            v___x_6413_ = crate::leanh::lean_box(0);
                            v_isShared_6414_ = v_isSharedCheck_6439_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_6440_ = crate::leanh::lean_ctor_get(v___x_6399_, 0);
                    v_a_6441_ = crate::leanh::lean_ctor_get(v___x_6399_, 1);
                    v_isSharedCheck_6448_ = (!crate::leanh::lean_is_exclusive(v___x_6399_)) as u8;
                    if v_isSharedCheck_6448_ == 0 {
                        v___x_6443_ = v___x_6399_;
                        v_isShared_6444_ = v_isSharedCheck_6448_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6441_);
                        crate::leanh::lean_inc(v_a_6440_);
                        crate::leanh::lean_dec(v___x_6399_);
                        v___x_6443_ = crate::leanh::lean_box(0);
                        v_isShared_6444_ = v_isSharedCheck_6448_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6405_ = crate::leanh::lean_box(0);
                if v_isShared_6404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6403_, 0, v___x_6405_);
                    v___x_6407_ = v___x_6403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6408_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6408_, 0, v___x_6405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6408_, 1, v_a_6401_);
                    v___x_6407_ = v_reuseFailAlloc_6408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6407_;
            }
            3 => {
                v_snd_6415_ = crate::leanh::lean_ctor_get(v_val_6411_, 1);
                crate::leanh::lean_inc(v_snd_6415_);
                crate::leanh::lean_dec(v_val_6411_);
                if crate::leanh::lean_obj_tag(v_snd_6415_) == 0 {
                    crate::leanh::lean_del_object(v___x_6413_);
                    v_a_6416_ = crate::leanh::lean_ctor_get(v___x_6399_, 1);
                    crate::leanh::lean_inc(v_a_6416_);
                    crate::leanh::lean_dec_ref_known(v___x_6399_, 2);
                    v_a_6417_ = crate::leanh::lean_ctor_get(v_snd_6415_, 0);
                    v_isSharedCheck_6425_ = (!crate::leanh::lean_is_exclusive(v_snd_6415_)) as u8;
                    if v_isSharedCheck_6425_ == 0 {
                        v___x_6419_ = v_snd_6415_;
                        v_isShared_6420_ = v_isSharedCheck_6425_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6417_);
                        crate::leanh::lean_dec(v_snd_6415_);
                        v___x_6419_ = crate::leanh::lean_box(0);
                        v_isShared_6420_ = v_isSharedCheck_6425_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_6426_ = crate::leanh::lean_ctor_get(v___x_6399_, 1);
                    crate::leanh::lean_inc(v_a_6426_);
                    crate::leanh::lean_dec_ref_known(v___x_6399_, 2);
                    v_a_6427_ = crate::leanh::lean_ctor_get(v_snd_6415_, 0);
                    v_isSharedCheck_6438_ = (!crate::leanh::lean_is_exclusive(v_snd_6415_)) as u8;
                    if v_isSharedCheck_6438_ == 0 {
                        v___x_6429_ = v_snd_6415_;
                        v_isShared_6430_ = v_isSharedCheck_6438_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6427_);
                        crate::leanh::lean_dec(v_snd_6415_);
                        v___x_6429_ = crate::leanh::lean_box(0);
                        v_isShared_6430_ = v_isSharedCheck_6438_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6420_ == 0 {
                    v___x_6422_ = v___x_6419_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6424_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6424_, 0, v_a_6417_);
                    v___x_6422_ = v_reuseFailAlloc_6424_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6423_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_6422_, v_a_6416_);
                crate::leanh::lean_dec_ref(v___x_6422_);
                return v___x_6423_;
            }
            6 => {
                if v_isShared_6414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6413_, 0, v_a_6427_);
                    v___x_6432_ = v___x_6413_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6437_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_a_6427_);
                    v___x_6432_ = v_reuseFailAlloc_6437_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_6430_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6429_, 0, v___x_6432_);
                    v___x_6434_ = v___x_6429_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6436_, 0, v___x_6432_);
                    v___x_6434_ = v_reuseFailAlloc_6436_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6435_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v___x_6434_, v_a_6426_);
                crate::leanh::lean_dec_ref(v___x_6434_);
                return v___x_6435_;
            }
            9 => {
                if v_isShared_6444_ == 0 {
                    v___x_6446_ = v___x_6443_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6447_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6447_, 0, v_a_6440_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6447_, 1, v_a_6441_);
                    v___x_6446_ = v_reuseFailAlloc_6447_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6446_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed(
    mut v_env_6449_: *mut crate::leanh::LeanObject,
    mut v_stx_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6453_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1(
            v_env_6449_,
            v_stx_6450_,
            v___y_6451_,
            v___y_6452_,
        );
    crate::leanh::lean_dec_ref(v___y_6451_);
    return v_res_6453_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(
    mut v_env_6454_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6455_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6456_: *mut crate::leanh::LeanObject,
    mut v_n_6457_: *mut crate::leanh::LeanObject,
    mut v___y_6458_: *mut crate::leanh::LeanObject,
    mut v___y_6459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6460_ = l_Lean_ResolveName_resolveNamespace(
        v_env_6454_,
        v_currNamespace_6455_,
        v_openDecls_6456_,
        v_n_6457_,
    );
    v___x_6461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6461_, 0, v___x_6460_);
    crate::leanh::lean_ctor_set(v___x_6461_, 1, v___y_6459_);
    return v___x_6461_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed(
    mut v_env_6462_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6463_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6464_: *mut crate::leanh::LeanObject,
    mut v_n_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6468_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3(
            v_env_6462_,
            v_currNamespace_6463_,
            v_openDecls_6464_,
            v_n_6465_,
            v___y_6466_,
            v___y_6467_,
        );
    crate::leanh::lean_dec_ref(v___y_6466_);
    return v_res_6468_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(
    mut v_as_6469_: *mut crate::leanh::LeanObject,
    mut v___y_6470_: *mut crate::leanh::LeanObject,
    mut v___y_6471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6486_: u8 = 0;
    let mut v___x_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: u8 = 0;
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_6469_) == 0 {
                    v___x_6473_ = crate::leanh::lean_box(0);
                    v___x_6474_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6474_, 0, v___x_6473_);
                    return v___x_6474_;
                } else {
                    v_head_6475_ = crate::leanh::lean_ctor_get(v_as_6469_, 0);
                    crate::leanh::lean_inc(v_head_6475_);
                    v_tail_6476_ = crate::leanh::lean_ctor_get(v_as_6469_, 1);
                    crate::leanh::lean_inc(v_tail_6476_);
                    crate::leanh::lean_dec_ref_known(v_as_6469_, 2);
                    v_fst_6477_ = crate::leanh::lean_ctor_get(v_head_6475_, 0);
                    crate::leanh::lean_inc(v_fst_6477_);
                    v_snd_6478_ = crate::leanh::lean_ctor_get(v_head_6475_, 1);
                    crate::leanh::lean_inc(v_snd_6478_);
                    crate::leanh::lean_dec(v_head_6475_);
                    v___x_6479_ = l_Lean_inheritedTraceOptions;
                    v___x_6480_ = lean_st_ref_get(v___x_6479_);
                    v___x_6481_ = lean_st_ref_get(v___y_6471_);
                    v_scopes_6482_ = crate::leanh::lean_ctor_get(v___x_6481_, 2);
                    crate::leanh::lean_inc(v_scopes_6482_);
                    crate::leanh::lean_dec(v___x_6481_);
                    v___x_6483_ = l_Lean_Elab_Command_instInhabitedScope_default;
                    v___x_6484_ = l_List_head_x21___redArg(v___x_6483_, v_scopes_6482_);
                    crate::leanh::lean_dec(v_scopes_6482_);
                    v_opts_6485_ = crate::leanh::lean_ctor_get(v___x_6484_, 1);
                    crate::leanh::lean_inc_ref(v_opts_6485_);
                    crate::leanh::lean_dec(v___x_6484_);
                    v_hasTrace_6486_ = crate::leanh::lean_ctor_get_uint8(
                        v_opts_6485_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_6486_ == 0 {
                        crate::leanh::lean_dec_ref(v_opts_6485_);
                        crate::leanh::lean_dec(v___x_6480_);
                        crate::leanh::lean_dec(v_snd_6478_);
                        crate::leanh::lean_dec(v_fst_6477_);
                        v_as_6469_ = v_tail_6476_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6488_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3___closed__11;
                        crate::leanh::lean_inc(v_fst_6477_);
                        v___x_6489_ = l_Lean_Name_append(v___x_6488_, v_fst_6477_);
                        v___x_6490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v___x_6480_,
                            v_opts_6485_,
                            v___x_6489_,
                        );
                        crate::leanh::lean_dec(v___x_6489_);
                        crate::leanh::lean_dec_ref(v_opts_6485_);
                        crate::leanh::lean_dec(v___x_6480_);
                        if v___x_6490_ == 0 {
                            crate::leanh::lean_dec(v_snd_6478_);
                            crate::leanh::lean_dec(v_fst_6477_);
                            v_as_6469_ = v_tail_6476_;
                            state = 0;
                            continue;
                        } else {
                            v___x_6492_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6492_, 0, v_snd_6478_);
                            v___x_6493_ = l_Lean_MessageData_ofFormat(v___x_6492_);
                            v___x_6494_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__0(v_fst_6477_, v___x_6493_, v___y_6470_, v___y_6471_);
                            if crate::leanh::lean_obj_tag(v___x_6494_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6494_, 1);
                                v_as_6469_ = v_tail_6476_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_6476_);
                                return v___x_6494_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4___boxed(
    mut v_as_6496_: *mut crate::leanh::LeanObject,
    mut v___y_6497_: *mut crate::leanh::LeanObject,
    mut v___y_6498_: *mut crate::leanh::LeanObject,
    mut v___y_6499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6500_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v_as_6496_, v___y_6497_, v___y_6498_);
    crate::leanh::lean_dec(v___y_6498_);
    crate::leanh::lean_dec_ref(v___y_6497_);
    return v_res_6500_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(
    mut v_env_6501_: *mut crate::leanh::LeanObject,
    mut v_opts_6502_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6503_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6504_: *mut crate::leanh::LeanObject,
    mut v_n_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
    mut v___y_6507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6508_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_6501_,
        v_opts_6502_,
        v_currNamespace_6503_,
        v_openDecls_6504_,
        v_n_6505_,
    );
    v___x_6509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6509_, 0, v___x_6508_);
    crate::leanh::lean_ctor_set(v___x_6509_, 1, v___y_6507_);
    return v___x_6509_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed(
    mut v_env_6510_: *mut crate::leanh::LeanObject,
    mut v_opts_6511_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_6512_: *mut crate::leanh::LeanObject,
    mut v_openDecls_6513_: *mut crate::leanh::LeanObject,
    mut v_n_6514_: *mut crate::leanh::LeanObject,
    mut v___y_6515_: *mut crate::leanh::LeanObject,
    mut v___y_6516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6517_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4(
            v_env_6510_,
            v_opts_6511_,
            v_currNamespace_6512_,
            v_openDecls_6513_,
            v_n_6514_,
            v___y_6515_,
            v___y_6516_,
        );
    crate::leanh::lean_dec_ref(v___y_6515_);
    crate::leanh::lean_dec_ref(v_opts_6511_);
    return v_res_6517_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(
    mut v_x_6519_: *mut crate::leanh::LeanObject,
    mut v___y_6520_: *mut crate::leanh::LeanObject,
    mut v___y_6521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_scopes_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_usedQuotCtxts_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6578_: u8 = 0;
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6586_: u8 = 0;
    let mut v___x_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6590_: u8 = 0;
    let mut v_unused_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6595_: u8 = 0;
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_reuseFailAlloc_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6601_: u8 = 0;
    let mut v_unused_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6606_: u8 = 0;
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6610_: u8 = 0;
    let mut v_a_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: u8 = 0;
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6627_: u8 = 0;
    let mut v___x_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6631_: u8 = 0;
    let mut v_a_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6635_: u8 = 0;
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6639_: u8 = 0;
    let mut v_a_6640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6643_: u8 = 0;
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6647_: u8 = 0;
    let mut v_a_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6523_ = lean_st_ref_get(v___y_6521_);
                v_env_6524_ = crate::leanh::lean_ctor_get(v___x_6523_, 0);
                crate::leanh::lean_inc_ref(v_env_6524_);
                crate::leanh::lean_dec(v___x_6523_);
                v___x_6525_ = lean_st_ref_get(v___y_6521_);
                v_scopes_6526_ = crate::leanh::lean_ctor_get(v___x_6525_, 2);
                crate::leanh::lean_inc(v_scopes_6526_);
                crate::leanh::lean_dec(v___x_6525_);
                v___x_6527_ = l_Lean_Elab_Command_instInhabitedScope_default;
                v___x_6528_ = l_List_head_x21___redArg(v___x_6527_, v_scopes_6526_);
                crate::leanh::lean_dec(v_scopes_6526_);
                v_opts_6529_ = crate::leanh::lean_ctor_get(v___x_6528_, 1);
                crate::leanh::lean_inc_ref(v_opts_6529_);
                crate::leanh::lean_dec(v___x_6528_);
                v___x_6530_ = l_Lean_Elab_Command_getScope___redArg(v___y_6521_);
                if crate::leanh::lean_obj_tag(v___x_6530_) == 0 {
                    v_a_6531_ = crate::leanh::lean_ctor_get(v___x_6530_, 0);
                    crate::leanh::lean_inc(v_a_6531_);
                    crate::leanh::lean_dec_ref_known(v___x_6530_, 1);
                    v_currNamespace_6532_ = crate::leanh::lean_ctor_get(v_a_6531_, 2);
                    crate::leanh::lean_inc(v_currNamespace_6532_);
                    crate::leanh::lean_dec(v_a_6531_);
                    v___x_6533_ = l_Lean_Elab_Command_getScope___redArg(v___y_6521_);
                    if crate::leanh::lean_obj_tag(v___x_6533_) == 0 {
                        v_a_6534_ = crate::leanh::lean_ctor_get(v___x_6533_, 0);
                        crate::leanh::lean_inc(v_a_6534_);
                        crate::leanh::lean_dec_ref_known(v___x_6533_, 1);
                        v_openDecls_6535_ = crate::leanh::lean_ctor_get(v_a_6534_, 3);
                        crate::leanh::lean_inc(v_openDecls_6535_);
                        crate::leanh::lean_dec(v_a_6534_);
                        v___x_6536_ = l_Lean_Elab_Command_getRef___redArg(v___y_6520_);
                        if crate::leanh::lean_obj_tag(v___x_6536_) == 0 {
                            v_a_6537_ = crate::leanh::lean_ctor_get(v___x_6536_, 0);
                            crate::leanh::lean_inc(v_a_6537_);
                            crate::leanh::lean_dec_ref_known(v___x_6536_, 1);
                            v___x_6538_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_6520_);
                            if crate::leanh::lean_obj_tag(v___x_6538_) == 0 {
                                v_a_6539_ = crate::leanh::lean_ctor_get(v___x_6538_, 0);
                                crate::leanh::lean_inc(v_a_6539_);
                                crate::leanh::lean_dec_ref_known(v___x_6538_, 1);
                                v_currRecDepth_6540_ = crate::leanh::lean_ctor_get(v___y_6520_, 2);
                                v_quotContext_x3f_6541_ =
                                    crate::leanh::lean_ctor_get(v___y_6520_, 5);
                                crate::leanh::lean_inc_ref_n(v_env_6524_, 3);
                                v___f_6542_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                                crate::leanh::lean_closure_set(v___f_6542_, 0, v_env_6524_);
                                v___f_6543_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                                crate::leanh::lean_closure_set(v___f_6543_, 0, v_env_6524_);
                                crate::leanh::lean_inc_n(v_currNamespace_6532_, 2);
                                v___f_6544_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 3, 1);
                                crate::leanh::lean_closure_set(
                                    v___f_6544_,
                                    0,
                                    v_currNamespace_6532_,
                                );
                                crate::leanh::lean_inc(v_openDecls_6535_);
                                v___f_6545_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                                crate::leanh::lean_closure_set(v___f_6545_, 0, v_env_6524_);
                                crate::leanh::lean_closure_set(
                                    v___f_6545_,
                                    1,
                                    v_currNamespace_6532_,
                                );
                                crate::leanh::lean_closure_set(v___f_6545_, 2, v_openDecls_6535_);
                                v___f_6546_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                                crate::leanh::lean_closure_set(v___f_6546_, 0, v_env_6524_);
                                crate::leanh::lean_closure_set(v___f_6546_, 1, v_opts_6529_);
                                crate::leanh::lean_closure_set(
                                    v___f_6546_,
                                    2,
                                    v_currNamespace_6532_,
                                );
                                crate::leanh::lean_closure_set(v___f_6546_, 3, v_openDecls_6535_);
                                v_methods_6547_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_methods_6547_, 0, v___f_6543_);
                                crate::leanh::lean_ctor_set(v_methods_6547_, 1, v___f_6544_);
                                crate::leanh::lean_ctor_set(v_methods_6547_, 2, v___f_6542_);
                                crate::leanh::lean_ctor_set(v_methods_6547_, 3, v___f_6545_);
                                crate::leanh::lean_ctor_set(v_methods_6547_, 4, v___f_6546_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_6541_) == 0 {
                                    v___x_6621_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_6521_);
                                    v_a_6622_ = crate::leanh::lean_ctor_get(v___x_6621_, 0);
                                    crate::leanh::lean_inc(v_a_6622_);
                                    crate::leanh::lean_dec_ref(v___x_6621_);
                                    v_a_6549_ = v_a_6622_;
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_6623_ =
                                        crate::leanh::lean_ctor_get(v_quotContext_x3f_6541_, 0);
                                    crate::leanh::lean_inc(v_val_6623_);
                                    v_a_6549_ = v_val_6623_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6537_);
                                crate::leanh::lean_dec(v_openDecls_6535_);
                                crate::leanh::lean_dec(v_currNamespace_6532_);
                                crate::leanh::lean_dec_ref(v_opts_6529_);
                                crate::leanh::lean_dec_ref(v_env_6524_);
                                crate::leanh::lean_dec_ref(v_x_6519_);
                                v_a_6624_ = crate::leanh::lean_ctor_get(v___x_6538_, 0);
                                v_isSharedCheck_6631_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6538_)) as u8;
                                if v_isSharedCheck_6631_ == 0 {
                                    v___x_6626_ = v___x_6538_;
                                    v_isShared_6627_ = v_isSharedCheck_6631_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6624_);
                                    crate::leanh::lean_dec(v___x_6538_);
                                    v___x_6626_ = crate::leanh::lean_box(0);
                                    v_isShared_6627_ = v_isSharedCheck_6631_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_openDecls_6535_);
                            crate::leanh::lean_dec(v_currNamespace_6532_);
                            crate::leanh::lean_dec_ref(v_opts_6529_);
                            crate::leanh::lean_dec_ref(v_env_6524_);
                            crate::leanh::lean_dec_ref(v_x_6519_);
                            v_a_6632_ = crate::leanh::lean_ctor_get(v___x_6536_, 0);
                            v_isSharedCheck_6639_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6536_)) as u8;
                            if v_isSharedCheck_6639_ == 0 {
                                v___x_6634_ = v___x_6536_;
                                v_isShared_6635_ = v_isSharedCheck_6639_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6632_);
                                crate::leanh::lean_dec(v___x_6536_);
                                v___x_6634_ = crate::leanh::lean_box(0);
                                v_isShared_6635_ = v_isSharedCheck_6639_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_currNamespace_6532_);
                        crate::leanh::lean_dec_ref(v_opts_6529_);
                        crate::leanh::lean_dec_ref(v_env_6524_);
                        crate::leanh::lean_dec_ref(v_x_6519_);
                        v_a_6640_ = crate::leanh::lean_ctor_get(v___x_6533_, 0);
                        v_isSharedCheck_6647_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6533_)) as u8;
                        if v_isSharedCheck_6647_ == 0 {
                            v___x_6642_ = v___x_6533_;
                            v_isShared_6643_ = v_isSharedCheck_6647_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6640_);
                            crate::leanh::lean_dec(v___x_6533_);
                            v___x_6642_ = crate::leanh::lean_box(0);
                            v_isShared_6643_ = v_isSharedCheck_6647_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_opts_6529_);
                    crate::leanh::lean_dec_ref(v_env_6524_);
                    crate::leanh::lean_dec_ref(v_x_6519_);
                    v_a_6648_ = crate::leanh::lean_ctor_get(v___x_6530_, 0);
                    v_isSharedCheck_6655_ = (!crate::leanh::lean_is_exclusive(v___x_6530_)) as u8;
                    if v_isSharedCheck_6655_ == 0 {
                        v___x_6650_ = v___x_6530_;
                        v_isShared_6651_ = v_isSharedCheck_6655_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6648_);
                        crate::leanh::lean_dec(v___x_6530_);
                        v___x_6650_ = crate::leanh::lean_box(0);
                        v_isShared_6651_ = v_isSharedCheck_6655_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6550_ = lean_st_ref_get(v___y_6521_);
                v_maxRecDepth_6551_ = crate::leanh::lean_ctor_get(v___x_6550_, 5);
                crate::leanh::lean_inc(v_maxRecDepth_6551_);
                crate::leanh::lean_dec(v___x_6550_);
                v___x_6552_ = lean_st_ref_get(v___y_6521_);
                v_nextMacroScope_6553_ = crate::leanh::lean_ctor_get(v___x_6552_, 4);
                crate::leanh::lean_inc(v_nextMacroScope_6553_);
                crate::leanh::lean_dec(v___x_6552_);
                crate::leanh::lean_inc(v_currRecDepth_6540_);
                v___x_6554_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6554_, 0, v_methods_6547_);
                crate::leanh::lean_ctor_set(v___x_6554_, 1, v_a_6549_);
                crate::leanh::lean_ctor_set(v___x_6554_, 2, v_a_6539_);
                crate::leanh::lean_ctor_set(v___x_6554_, 3, v_currRecDepth_6540_);
                crate::leanh::lean_ctor_set(v___x_6554_, 4, v_maxRecDepth_6551_);
                crate::leanh::lean_ctor_set(v___x_6554_, 5, v_a_6537_);
                v___x_6555_ = crate::leanh::lean_box(0);
                v___x_6556_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6556_, 0, v_nextMacroScope_6553_);
                crate::leanh::lean_ctor_set(v___x_6556_, 1, v___x_6555_);
                crate::leanh::lean_ctor_set(v___x_6556_, 2, v___x_6555_);
                v___x_6557_ = crate::leanh::lean_apply_2(v_x_6519_, v___x_6554_, v___x_6556_);
                if crate::leanh::lean_obj_tag(v___x_6557_) == 0 {
                    v_a_6558_ = crate::leanh::lean_ctor_get(v___x_6557_, 1);
                    crate::leanh::lean_inc(v_a_6558_);
                    v_a_6559_ = crate::leanh::lean_ctor_get(v___x_6557_, 0);
                    crate::leanh::lean_inc(v_a_6559_);
                    crate::leanh::lean_dec_ref_known(v___x_6557_, 2);
                    v_macroScope_6560_ = crate::leanh::lean_ctor_get(v_a_6558_, 0);
                    crate::leanh::lean_inc(v_macroScope_6560_);
                    v_traceMsgs_6561_ = crate::leanh::lean_ctor_get(v_a_6558_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_6561_);
                    v_expandedMacroDecls_6562_ = crate::leanh::lean_ctor_get(v_a_6558_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_6562_);
                    crate::leanh::lean_dec(v_a_6558_);
                    v___x_6563_ = crate::leanh::lean_box(0);
                    v___x_6564_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_expandedMacroDecls_6562_, v___x_6563_, v___y_6520_, v___y_6521_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_6562_);
                    if crate::leanh::lean_obj_tag(v___x_6564_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6564_, 1);
                        v___x_6565_ = lean_st_ref_take(v___y_6521_);
                        v_env_6566_ = crate::leanh::lean_ctor_get(v___x_6565_, 0);
                        v_messages_6567_ = crate::leanh::lean_ctor_get(v___x_6565_, 1);
                        v_scopes_6568_ = crate::leanh::lean_ctor_get(v___x_6565_, 2);
                        v_usedQuotCtxts_6569_ = crate::leanh::lean_ctor_get(v___x_6565_, 3);
                        v_maxRecDepth_6570_ = crate::leanh::lean_ctor_get(v___x_6565_, 5);
                        v_ngen_6571_ = crate::leanh::lean_ctor_get(v___x_6565_, 6);
                        v_auxDeclNGen_6572_ = crate::leanh::lean_ctor_get(v___x_6565_, 7);
                        v_infoState_6573_ = crate::leanh::lean_ctor_get(v___x_6565_, 8);
                        v_traceState_6574_ = crate::leanh::lean_ctor_get(v___x_6565_, 9);
                        v_snapshotTasks_6575_ = crate::leanh::lean_ctor_get(v___x_6565_, 10);
                        v_isSharedCheck_6601_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6565_)) as u8;
                        if v_isSharedCheck_6601_ == 0 {
                            v_unused_6602_ = crate::leanh::lean_ctor_get(v___x_6565_, 4);
                            crate::leanh::lean_dec(v_unused_6602_);
                            v___x_6577_ = v___x_6565_;
                            v_isShared_6578_ = v_isSharedCheck_6601_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_6575_);
                            crate::leanh::lean_inc(v_traceState_6574_);
                            crate::leanh::lean_inc(v_infoState_6573_);
                            crate::leanh::lean_inc(v_auxDeclNGen_6572_);
                            crate::leanh::lean_inc(v_ngen_6571_);
                            crate::leanh::lean_inc(v_maxRecDepth_6570_);
                            crate::leanh::lean_inc(v_usedQuotCtxts_6569_);
                            crate::leanh::lean_inc(v_scopes_6568_);
                            crate::leanh::lean_inc(v_messages_6567_);
                            crate::leanh::lean_inc(v_env_6566_);
                            crate::leanh::lean_dec(v___x_6565_);
                            v___x_6577_ = crate::leanh::lean_box(0);
                            v_isShared_6578_ = v_isSharedCheck_6601_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_6561_);
                        crate::leanh::lean_dec(v_macroScope_6560_);
                        crate::leanh::lean_dec(v_a_6559_);
                        v_a_6603_ = crate::leanh::lean_ctor_get(v___x_6564_, 0);
                        v_isSharedCheck_6610_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6564_)) as u8;
                        if v_isSharedCheck_6610_ == 0 {
                            v___x_6605_ = v___x_6564_;
                            v_isShared_6606_ = v_isSharedCheck_6610_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6603_);
                            crate::leanh::lean_dec(v___x_6564_);
                            v___x_6605_ = crate::leanh::lean_box(0);
                            v_isShared_6606_ = v_isSharedCheck_6610_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v_a_6611_ = crate::leanh::lean_ctor_get(v___x_6557_, 0);
                    crate::leanh::lean_inc(v_a_6611_);
                    crate::leanh::lean_dec_ref_known(v___x_6557_, 2);
                    if crate::leanh::lean_obj_tag(v_a_6611_) == 0 {
                        v_a_6612_ = crate::leanh::lean_ctor_get(v_a_6611_, 0);
                        crate::leanh::lean_inc(v_a_6612_);
                        v_a_6613_ = crate::leanh::lean_ctor_get(v_a_6611_, 1);
                        crate::leanh::lean_inc_ref(v_a_6613_);
                        crate::leanh::lean_dec_ref_known(v_a_6611_, 2);
                        v___x_6614_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___closed__0;
                        v___x_6615_ = lean_string_dec_eq(v_a_6613_, v___x_6614_);
                        if v___x_6615_ == 0 {
                            v___x_6616_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6616_, 0, v_a_6613_);
                            v___x_6617_ = l_Lean_MessageData_ofFormat(v___x_6616_);
                            v___x_6618_ = l_Lean_throwErrorAt___at___00Lean_Elab_Command_elabElabRulesAux_spec__3___redArg(v_a_6612_, v___x_6617_, v___y_6520_, v___y_6521_);
                            crate::leanh::lean_dec(v_a_6612_);
                            return v___x_6618_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_6613_);
                            v___x_6619_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_a_6612_);
                            return v___x_6619_;
                        }
                    } else {
                        v___x_6620_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_6620_;
                    }
                }
            }
            2 => {
                if v_isShared_6578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6577_, 4, v_macroScope_6560_);
                    v___x_6580_ = v___x_6577_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6600_ = crate::leanh::lean_alloc_ctor(0, 11, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 0, v_env_6566_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 1, v_messages_6567_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 2, v_scopes_6568_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 3, v_usedQuotCtxts_6569_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 4, v_macroScope_6560_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 5, v_maxRecDepth_6570_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 6, v_ngen_6571_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 7, v_auxDeclNGen_6572_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 8, v_infoState_6573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 9, v_traceState_6574_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6600_, 10, v_snapshotTasks_6575_);
                    v___x_6580_ = v_reuseFailAlloc_6600_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6581_ = lean_st_ref_set(v___y_6521_, v___x_6580_);
                v___x_6582_ = l_List_reverse___redArg(v_traceMsgs_6561_);
                v___x_6583_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__4(v___x_6582_, v___y_6520_, v___y_6521_);
                if crate::leanh::lean_obj_tag(v___x_6583_) == 0 {
                    v_isSharedCheck_6590_ = (!crate::leanh::lean_is_exclusive(v___x_6583_)) as u8;
                    if v_isSharedCheck_6590_ == 0 {
                        v_unused_6591_ = crate::leanh::lean_ctor_get(v___x_6583_, 0);
                        crate::leanh::lean_dec(v_unused_6591_);
                        v___x_6585_ = v___x_6583_;
                        v_isShared_6586_ = v_isSharedCheck_6590_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6583_);
                        v___x_6585_ = crate::leanh::lean_box(0);
                        v_isShared_6586_ = v_isSharedCheck_6590_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6559_);
                    v_a_6592_ = crate::leanh::lean_ctor_get(v___x_6583_, 0);
                    v_isSharedCheck_6599_ = (!crate::leanh::lean_is_exclusive(v___x_6583_)) as u8;
                    if v_isSharedCheck_6599_ == 0 {
                        v___x_6594_ = v___x_6583_;
                        v_isShared_6595_ = v_isSharedCheck_6599_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6592_);
                        crate::leanh::lean_dec(v___x_6583_);
                        v___x_6594_ = crate::leanh::lean_box(0);
                        v_isShared_6595_ = v_isSharedCheck_6599_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_6586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6585_, 0, v_a_6559_);
                    v___x_6588_ = v___x_6585_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6589_, 0, v_a_6559_);
                    v___x_6588_ = v_reuseFailAlloc_6589_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6588_;
            }
            6 => {
                if v_isShared_6595_ == 0 {
                    v___x_6597_ = v___x_6594_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v_a_6592_);
                    v___x_6597_ = v_reuseFailAlloc_6598_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6597_;
            }
            8 => {
                if v_isShared_6606_ == 0 {
                    v___x_6608_ = v___x_6605_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6609_, 0, v_a_6603_);
                    v___x_6608_ = v_reuseFailAlloc_6609_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6608_;
            }
            10 => {
                if v_isShared_6627_ == 0 {
                    v___x_6629_ = v___x_6626_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6630_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6630_, 0, v_a_6624_);
                    v___x_6629_ = v_reuseFailAlloc_6630_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6629_;
            }
            12 => {
                if v_isShared_6635_ == 0 {
                    v___x_6637_ = v___x_6634_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_a_6632_);
                    v___x_6637_ = v_reuseFailAlloc_6638_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6637_;
            }
            14 => {
                if v_isShared_6643_ == 0 {
                    v___x_6645_ = v___x_6642_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6646_, 0, v_a_6640_);
                    v___x_6645_ = v_reuseFailAlloc_6646_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6645_;
            }
            16 => {
                if v_isShared_6651_ == 0 {
                    v___x_6653_ = v___x_6650_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6654_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6654_, 0, v_a_6648_);
                    v___x_6653_ = v_reuseFailAlloc_6654_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg___boxed(
    mut v_x_6656_: *mut crate::leanh::LeanObject,
    mut v___y_6657_: *mut crate::leanh::LeanObject,
    mut v___y_6658_: *mut crate::leanh::LeanObject,
    mut v___y_6659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6660_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(
        v_x_6656_,
        v___y_6657_,
        v___y_6658_,
    );
    crate::leanh::lean_dec(v___y_6658_);
    crate::leanh::lean_dec_ref(v___y_6657_);
    return v_res_6660_;
}
pub unsafe fn l_Lean_Elab_Command_elabElab(
    mut v_x_6700_: *mut crate::leanh::LeanObject,
    mut v_a_6701_: *mut crate::leanh::LeanObject,
    mut v_a_6702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: u8 = 0;
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6800_: u8 = 0;
    let mut v___y_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6818_: usize = 0;
    let mut v___y_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6839_: usize = 0;
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6870_: u8 = 0;
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6874_: u8 = 0;
    let mut v_a_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6878_: u8 = 0;
    let mut v___x_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6882_: u8 = 0;
    let mut v_a_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6886_: u8 = 0;
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6890_: u8 = 0;
    let mut v___y_6892_: u8 = 0;
    let mut v___y_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6910_: usize = 0;
    let mut v___y_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6932_: u8 = 0;
    let mut v___y_6933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6950_: usize = 0;
    let mut v___y_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6968_: u8 = 0;
    let mut v___y_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6986_: usize = 0;
    let mut v___y_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7007_: u8 = 0;
    let mut v___y_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7021_: usize = 0;
    let mut v___y_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7053_: usize = 0;
    let mut v___x_7054_: usize = 0;
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_x3f_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: u8 = 0;
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7071_: u8 = 0;
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7075_: u8 = 0;
    let mut v_a_7076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___x_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7083_: u8 = 0;
    let mut v_a_7084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7087_: u8 = 0;
    let mut v___x_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7091_: u8 = 0;
    let mut v_a_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7095_: u8 = 0;
    let mut v___x_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7099_: u8 = 0;
    let mut v___y_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_7112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: u8 = 0;
    let mut v___x_7119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: u8 = 0;
    let mut v___x_7125_: u8 = 0;
    let mut v___x_7126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expectedType_x3f_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7147_: u8 = 0;
    let mut v___x_7148_: u8 = 0;
    let mut v___x_7149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: u8 = 0;
    let mut v___x_7153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prio_x3f_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_7168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: u8 = 0;
    let mut v___x_7174_: u8 = 0;
    let mut v___x_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: u8 = 0;
    let mut v___x_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_x3f_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7193_: u8 = 0;
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tk_7196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: u8 = 0;
    let mut v___x_7200_: u8 = 0;
    let mut v___x_7201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: u8 = 0;
    let mut v___x_7205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prec_x3f_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: u8 = 0;
    let mut v___x_7216_: u8 = 0;
    let mut v___x_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: u8 = 0;
    let mut v___x_7221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_x3f_7223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7227_: u8 = 0;
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: u8 = 0;
    let mut v___x_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_doc_x3f_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: u8 = 0;
    let mut v___x_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6704_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__0;
                v___x_6705_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__1;
                v___x_6746_ = l_Lean_Elab_Command_elabElab___closed__3;
                crate::leanh::lean_inc(v_x_6700_);
                v___x_6747_ = l_Lean_Syntax_isOfKind(v_x_6700_, v___x_6746_);
                if v___x_6747_ == 0 {
                    crate::leanh::lean_dec(v_x_6700_);
                    v___x_6748_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_6748_;
                } else {
                    v___x_6749_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_7226_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_6749_);
                    v___x_7227_ = l_Lean_Syntax_isNone(v___x_7226_);
                    if v___x_7227_ == 0 {
                        v___x_7228_ = crate::leanh::lean_unsigned_to_nat(1);
                        crate::leanh::lean_inc(v___x_7226_);
                        v___x_7229_ = l_Lean_Syntax_matchesNull(v___x_7226_, v___x_7228_);
                        if v___x_7229_ == 0 {
                            crate::leanh::lean_dec(v___x_7226_);
                            crate::leanh::lean_dec(v_x_6700_);
                            v___x_7230_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_7230_;
                        } else {
                            v_doc_x3f_7231_ = l_Lean_Syntax_getArg(v___x_7226_, v___x_6749_);
                            crate::leanh::lean_dec(v___x_7226_);
                            v___x_7232_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__7;
                            crate::leanh::lean_inc(v_doc_x3f_7231_);
                            v___x_7233_ = l_Lean_Syntax_isOfKind(v_doc_x3f_7231_, v___x_7232_);
                            if v___x_7233_ == 0 {
                                crate::leanh::lean_dec(v_doc_x3f_7231_);
                                crate::leanh::lean_dec(v_x_6700_);
                                v___x_7234_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                                return v___x_7234_;
                            } else {
                                v___x_7235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7235_, 0, v_doc_x3f_7231_);
                                v_doc_x3f_7210_ = v___x_7235_;
                                v___y_7211_ = v_a_6701_;
                                v___y_7212_ = v_a_6702_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7226_);
                        v___x_7236_ = crate::leanh::lean_box(0);
                        v_doc_x3f_7210_ = v___x_7236_;
                        v___y_7211_ = v_a_6701_;
                        v___y_7212_ = v_a_6702_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_6712_);
                v___x_6723_ = l_Array_append___redArg(v___y_6712_, v___y_6722_);
                crate::leanh::lean_dec_ref(v___y_6722_);
                crate::leanh::lean_inc_n(v___y_6720_, 4);
                crate::leanh::lean_inc_n(v___y_6710_, 11);
                v___x_6724_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6724_, 0, v___y_6710_);
                crate::leanh::lean_ctor_set(v___x_6724_, 1, v___y_6720_);
                crate::leanh::lean_ctor_set(v___x_6724_, 2, v___x_6723_);
                v___x_6725_ = l_Lean_Elab_Command_elabElabRulesAux___closed__22;
                crate::leanh::lean_inc_ref_n(v___y_6713_, 3);
                v___x_6726_ =
                    l_Lean_Name_mkStr4(v___x_6704_, v___x_6705_, v___y_6713_, v___x_6725_);
                v___x_6727_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__4;
                v___x_6728_ =
                    l_Lean_Name_mkStr4(v___x_6704_, v___x_6705_, v___y_6713_, v___x_6727_);
                v___x_6729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__6;
                v___x_6730_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6730_, 0, v___y_6710_);
                crate::leanh::lean_ctor_set(v___x_6730_, 1, v___x_6729_);
                v___x_6731_ = l_Lean_Elab_Command_elabElab___closed__0;
                v___x_6732_ =
                    l_Lean_Name_mkStr4(v___x_6704_, v___x_6705_, v___y_6713_, v___x_6731_);
                v___x_6733_ = l_Lean_Elab_Command_elabElab___closed__1;
                v___x_6734_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6734_, 0, v___y_6710_);
                crate::leanh::lean_ctor_set(v___x_6734_, 1, v___x_6733_);
                crate::leanh::lean_inc_ref(v___y_6711_);
                v___x_6735_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6735_, 0, v___y_6710_);
                crate::leanh::lean_ctor_set(v___x_6735_, 1, v___y_6711_);
                v___x_6736_ = l_Lean_Syntax_node3(
                    v___y_6710_,
                    v___x_6732_,
                    v___x_6734_,
                    v___y_6719_,
                    v___x_6735_,
                );
                v___x_6737_ = l_Lean_Syntax_node1(v___y_6710_, v___y_6720_, v___x_6736_);
                v___x_6738_ = l_Lean_Syntax_node1(v___y_6710_, v___y_6720_, v___x_6737_);
                v___x_6739_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__8;
                v___x_6740_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6740_, 0, v___y_6710_);
                crate::leanh::lean_ctor_set(v___x_6740_, 1, v___x_6739_);
                v___x_6741_ = l_Lean_Syntax_node4(
                    v___y_6710_,
                    v___x_6728_,
                    v___x_6730_,
                    v___x_6738_,
                    v___x_6740_,
                    v___y_6714_,
                );
                v___x_6742_ = l_Lean_Syntax_node1(v___y_6710_, v___y_6720_, v___x_6741_);
                v___x_6743_ = l_Lean_Syntax_node1(v___y_6710_, v___x_6726_, v___x_6742_);
                crate::leanh::lean_inc(v___y_6715_);
                crate::leanh::lean_inc(v___y_6716_);
                v___x_6744_ = l_Lean_Syntax_node8(
                    v___y_6710_,
                    v___y_6716_,
                    v___y_6709_,
                    v___y_6715_,
                    v___y_6707_,
                    v___y_6721_,
                    v___y_6715_,
                    v___y_6708_,
                    v___x_6724_,
                    v___x_6743_,
                );
                v___x_6745_ =
                    l_Lean_Elab_Command_elabCommand(v___x_6744_, v___y_6718_, v___y_6717_);
                return v___x_6745_;
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v___y_6754_, 2);
                v___x_6767_ = l_Array_append___redArg(v___y_6754_, v___y_6766_);
                crate::leanh::lean_dec_ref(v___y_6766_);
                crate::leanh::lean_inc_n(v___y_6763_, 3);
                crate::leanh::lean_inc_n(v___y_6752_, 6);
                v___x_6768_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6768_, 0, v___y_6752_);
                crate::leanh::lean_ctor_set(v___x_6768_, 1, v___y_6763_);
                crate::leanh::lean_ctor_set(v___x_6768_, 2, v___x_6767_);
                v___x_6769_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6769_, 0, v___y_6752_);
                crate::leanh::lean_ctor_set(v___x_6769_, 1, v___y_6763_);
                crate::leanh::lean_ctor_set(v___x_6769_, 2, v___y_6754_);
                crate::leanh::lean_inc_ref(v___x_6769_);
                crate::leanh::lean_inc(v___y_6751_);
                v___x_6770_ = l_Lean_Syntax_node1(v___y_6752_, v___y_6751_, v___x_6769_);
                crate::leanh::lean_inc_ref(v___y_6765_);
                v___x_6771_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6771_, 0, v___y_6752_);
                crate::leanh::lean_ctor_set(v___x_6771_, 1, v___y_6765_);
                crate::leanh::lean_inc_ref(v___y_6764_);
                v___x_6772_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6772_, 0, v___y_6752_);
                crate::leanh::lean_ctor_set(v___x_6772_, 1, v___y_6764_);
                v___x_6773_ =
                    l_Lean_Syntax_node2(v___y_6752_, v___y_6763_, v___x_6772_, v___y_6757_);
                if crate::leanh::lean_obj_tag(v___y_6762_) == 1 {
                    v_val_6774_ = crate::leanh::lean_ctor_get(v___y_6762_, 0);
                    crate::leanh::lean_inc(v_val_6774_);
                    crate::leanh::lean_dec_ref_known(v___y_6762_, 1);
                    v___x_6775_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__0;
                    crate::leanh::lean_inc(v___y_6752_);
                    v___x_6776_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6776_, 0, v___y_6752_);
                    crate::leanh::lean_ctor_set(v___x_6776_, 1, v___x_6775_);
                    v___x_6777_ = l_Array_mkArray2___redArg(v___x_6776_, v_val_6774_);
                    v___y_6707_ = v___x_6770_;
                    v___y_6708_ = v___x_6773_;
                    v___y_6709_ = v___x_6768_;
                    v___y_6710_ = v___y_6752_;
                    v___y_6711_ = v___y_6753_;
                    v___y_6712_ = v___y_6754_;
                    v___y_6713_ = v___y_6755_;
                    v___y_6714_ = v___y_6756_;
                    v___y_6715_ = v___x_6769_;
                    v___y_6716_ = v___y_6758_;
                    v___y_6717_ = v___y_6759_;
                    v___y_6718_ = v___y_6761_;
                    v___y_6719_ = v___y_6760_;
                    v___y_6720_ = v___y_6763_;
                    v___y_6721_ = v___x_6771_;
                    v___y_6722_ = v___x_6777_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6762_);
                    v___x_6778_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_6707_ = v___x_6770_;
                    v___y_6708_ = v___x_6773_;
                    v___y_6709_ = v___x_6768_;
                    v___y_6710_ = v___y_6752_;
                    v___y_6711_ = v___y_6753_;
                    v___y_6712_ = v___y_6754_;
                    v___y_6713_ = v___y_6755_;
                    v___y_6714_ = v___y_6756_;
                    v___y_6715_ = v___x_6769_;
                    v___y_6716_ = v___y_6758_;
                    v___y_6717_ = v___y_6759_;
                    v___y_6718_ = v___y_6761_;
                    v___y_6719_ = v___y_6760_;
                    v___y_6720_ = v___y_6763_;
                    v___y_6721_ = v___x_6771_;
                    v___y_6722_ = v___x_6778_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_6794_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__0;
                v___x_6795_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__1;
                if crate::leanh::lean_obj_tag(v___y_6793_) == 1 {
                    v_val_6796_ = crate::leanh::lean_ctor_get(v___y_6793_, 0);
                    crate::leanh::lean_inc(v_val_6796_);
                    crate::leanh::lean_dec_ref_known(v___y_6793_, 1);
                    v___x_6797_ = l_Array_mkArray1___redArg(v_val_6796_);
                    v___y_6751_ = v___y_6780_;
                    v___y_6752_ = v___y_6781_;
                    v___y_6753_ = v___y_6782_;
                    v___y_6754_ = v___y_6783_;
                    v___y_6755_ = v___y_6784_;
                    v___y_6756_ = v___y_6785_;
                    v___y_6757_ = v___y_6786_;
                    v___y_6758_ = v___x_6795_;
                    v___y_6759_ = v___y_6787_;
                    v___y_6760_ = v___y_6788_;
                    v___y_6761_ = v___y_6789_;
                    v___y_6762_ = v___y_6790_;
                    v___y_6763_ = v___y_6791_;
                    v___y_6764_ = v___y_6792_;
                    v___y_6765_ = v___x_6794_;
                    v___y_6766_ = v___x_6797_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6793_);
                    v___x_6798_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_6751_ = v___y_6780_;
                    v___y_6752_ = v___y_6781_;
                    v___y_6753_ = v___y_6782_;
                    v___y_6754_ = v___y_6783_;
                    v___y_6755_ = v___y_6784_;
                    v___y_6756_ = v___y_6785_;
                    v___y_6757_ = v___y_6786_;
                    v___y_6758_ = v___x_6795_;
                    v___y_6759_ = v___y_6787_;
                    v___y_6760_ = v___y_6788_;
                    v___y_6761_ = v___y_6789_;
                    v___y_6762_ = v___y_6790_;
                    v___y_6763_ = v___y_6791_;
                    v___y_6764_ = v___y_6792_;
                    v___y_6765_ = v___x_6794_;
                    v___y_6766_ = v___x_6798_;
                    state = 2;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref_n(v___y_6803_, 2);
                v___x_6823_ = l_Array_append___redArg(v___y_6803_, v___y_6822_);
                crate::leanh::lean_dec_ref(v___y_6822_);
                crate::leanh::lean_inc_n(v___y_6812_, 3);
                crate::leanh::lean_inc_n(v___y_6815_, 9);
                v___x_6824_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6824_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6824_, 1, v___y_6812_);
                crate::leanh::lean_ctor_set(v___x_6824_, 2, v___x_6823_);
                v___x_6825_ = l_Lean_Elab_Command_elabElab___closed__5;
                v___x_6826_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__1;
                v___x_6827_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6827_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6827_, 1, v___x_6826_);
                v___x_6828_ = l_Lean_Elab_Command_elabElab___closed__6;
                v___x_6829_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6829_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6829_, 1, v___x_6828_);
                v___x_6830_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                v___x_6831_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6831_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6831_, 1, v___x_6830_);
                v___x_6832_ = l_Nat_reprFast(v___y_6811_);
                v___x_6833_ = crate::leanh::lean_box(2);
                v___x_6834_ = l_Lean_Syntax_mkNumLit(v___x_6832_, v___x_6833_);
                v___x_6835_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__3;
                v___x_6836_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6836_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6836_, 1, v___x_6835_);
                v___x_6837_ = l_Lean_Syntax_node5(
                    v___y_6815_,
                    v___x_6825_,
                    v___x_6827_,
                    v___x_6829_,
                    v___x_6831_,
                    v___x_6834_,
                    v___x_6836_,
                );
                v___x_6838_ = l_Lean_Syntax_node1(v___y_6815_, v___y_6812_, v___x_6837_);
                v_sz_6839_ = lean_array_size(v___y_6816_);
                v___x_6840_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__2(v_sz_6839_, v___y_6818_, v___y_6816_);
                v___x_6841_ = l_Array_append___redArg(v___y_6803_, v___x_6840_);
                crate::leanh::lean_dec_ref(v___x_6840_);
                v___x_6842_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6842_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6842_, 1, v___y_6812_);
                crate::leanh::lean_ctor_set(v___x_6842_, 2, v___x_6841_);
                v___x_6843_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                v___x_6844_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6844_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6844_, 1, v___x_6843_);
                v___x_6845_ = crate::leanh::lean_unsigned_to_nat(10);
                v___x_6846_ = lean_mk_empty_array_with_capacity(v___x_6845_);
                v___x_6847_ = lean_array_push(v___x_6846_, v___y_6817_);
                v___x_6848_ = lean_array_push(v___x_6847_, v___y_6802_);
                v___x_6849_ = lean_array_push(v___x_6848_, v___y_6821_);
                v___x_6850_ = lean_array_push(v___x_6849_, v___y_6813_);
                v___x_6851_ = lean_array_push(v___x_6850_, v___y_6808_);
                v___x_6852_ = lean_array_push(v___x_6851_, v___x_6824_);
                v___x_6853_ = lean_array_push(v___x_6852_, v___x_6838_);
                v___x_6854_ = lean_array_push(v___x_6853_, v___x_6842_);
                v___x_6855_ = lean_array_push(v___x_6854_, v___x_6844_);
                crate::leanh::lean_inc(v___y_6806_);
                v___x_6856_ = lean_array_push(v___x_6855_, v___y_6806_);
                crate::leanh::lean_inc(v___y_6819_);
                v___x_6857_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6857_, 0, v___y_6815_);
                crate::leanh::lean_ctor_set(v___x_6857_, 1, v___y_6819_);
                crate::leanh::lean_ctor_set(v___x_6857_, 2, v___x_6856_);
                v___x_6858_ = l_Lean_Elab_Command_elabSyntax(v___x_6857_, v___y_6809_, v___y_6807_);
                if crate::leanh::lean_obj_tag(v___x_6858_) == 0 {
                    v_a_6859_ = crate::leanh::lean_ctor_get(v___x_6858_, 0);
                    crate::leanh::lean_inc(v_a_6859_);
                    crate::leanh::lean_dec_ref_known(v___x_6858_, 1);
                    v___x_6860_ = l_Lean_Elab_Command_getRef___redArg(v___y_6809_);
                    if crate::leanh::lean_obj_tag(v___x_6860_) == 0 {
                        v_a_6861_ = crate::leanh::lean_ctor_get(v___x_6860_, 0);
                        crate::leanh::lean_inc(v_a_6861_);
                        crate::leanh::lean_dec_ref_known(v___x_6860_, 1);
                        v___x_6862_ = l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_6809_);
                        if crate::leanh::lean_obj_tag(v___x_6862_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6862_, 1);
                            v_quotContext_x3f_6863_ = crate::leanh::lean_ctor_get(v___y_6809_, 5);
                            v___x_6864_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6864_, 0, v___x_6833_);
                            crate::leanh::lean_ctor_set(v___x_6864_, 1, v_a_6859_);
                            crate::leanh::lean_ctor_set(v___x_6864_, 2, v___y_6820_);
                            v___x_6865_ = l_Lean_SourceInfo_fromRef(v_a_6861_, v___y_6800_);
                            crate::leanh::lean_dec(v_a_6861_);
                            if crate::leanh::lean_obj_tag(v_quotContext_x3f_6863_) == 0 {
                                v___x_6866_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_6807_);
                                crate::leanh::lean_dec_ref(v___x_6866_);
                                v___y_6780_ = v___y_6801_;
                                v___y_6781_ = v___x_6865_;
                                v___y_6782_ = v___x_6835_;
                                v___y_6783_ = v___y_6803_;
                                v___y_6784_ = v___y_6805_;
                                v___y_6785_ = v___y_6804_;
                                v___y_6786_ = v___y_6806_;
                                v___y_6787_ = v___y_6807_;
                                v___y_6788_ = v___x_6864_;
                                v___y_6789_ = v___y_6809_;
                                v___y_6790_ = v___y_6810_;
                                v___y_6791_ = v___y_6812_;
                                v___y_6792_ = v___x_6843_;
                                v___y_6793_ = v___y_6814_;
                                state = 3;
                                continue;
                            } else {
                                v___y_6780_ = v___y_6801_;
                                v___y_6781_ = v___x_6865_;
                                v___y_6782_ = v___x_6835_;
                                v___y_6783_ = v___y_6803_;
                                v___y_6784_ = v___y_6805_;
                                v___y_6785_ = v___y_6804_;
                                v___y_6786_ = v___y_6806_;
                                v___y_6787_ = v___y_6807_;
                                v___y_6788_ = v___x_6864_;
                                v___y_6789_ = v___y_6809_;
                                v___y_6790_ = v___y_6810_;
                                v___y_6791_ = v___y_6812_;
                                v___y_6792_ = v___x_6843_;
                                v___y_6793_ = v___y_6814_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6861_);
                            crate::leanh::lean_dec(v_a_6859_);
                            crate::leanh::lean_dec_ref(v___y_6820_);
                            crate::leanh::lean_dec(v___y_6814_);
                            crate::leanh::lean_dec(v___y_6810_);
                            crate::leanh::lean_dec(v___y_6806_);
                            crate::leanh::lean_dec(v___y_6804_);
                            v_a_6867_ = crate::leanh::lean_ctor_get(v___x_6862_, 0);
                            v_isSharedCheck_6874_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6862_)) as u8;
                            if v_isSharedCheck_6874_ == 0 {
                                v___x_6869_ = v___x_6862_;
                                v_isShared_6870_ = v_isSharedCheck_6874_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6867_);
                                crate::leanh::lean_dec(v___x_6862_);
                                v___x_6869_ = crate::leanh::lean_box(0);
                                v_isShared_6870_ = v_isSharedCheck_6874_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6859_);
                        crate::leanh::lean_dec_ref(v___y_6820_);
                        crate::leanh::lean_dec(v___y_6814_);
                        crate::leanh::lean_dec(v___y_6810_);
                        crate::leanh::lean_dec(v___y_6806_);
                        crate::leanh::lean_dec(v___y_6804_);
                        v_a_6875_ = crate::leanh::lean_ctor_get(v___x_6860_, 0);
                        v_isSharedCheck_6882_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6860_)) as u8;
                        if v_isSharedCheck_6882_ == 0 {
                            v___x_6877_ = v___x_6860_;
                            v_isShared_6878_ = v_isSharedCheck_6882_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6875_);
                            crate::leanh::lean_dec(v___x_6860_);
                            v___x_6877_ = crate::leanh::lean_box(0);
                            v_isShared_6878_ = v_isSharedCheck_6882_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6820_);
                    crate::leanh::lean_dec(v___y_6814_);
                    crate::leanh::lean_dec(v___y_6810_);
                    crate::leanh::lean_dec(v___y_6806_);
                    crate::leanh::lean_dec(v___y_6804_);
                    v_a_6883_ = crate::leanh::lean_ctor_get(v___x_6858_, 0);
                    v_isSharedCheck_6890_ = (!crate::leanh::lean_is_exclusive(v___x_6858_)) as u8;
                    if v_isSharedCheck_6890_ == 0 {
                        v___x_6885_ = v___x_6858_;
                        v_isShared_6886_ = v_isSharedCheck_6890_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6883_);
                        crate::leanh::lean_dec(v___x_6858_);
                        v___x_6885_ = crate::leanh::lean_box(0);
                        v_isShared_6886_ = v_isSharedCheck_6890_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6870_ == 0 {
                    v___x_6872_ = v___x_6869_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6873_, 0, v_a_6867_);
                    v___x_6872_ = v_reuseFailAlloc_6873_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6872_;
            }
            7 => {
                if v_isShared_6878_ == 0 {
                    v___x_6880_ = v___x_6877_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6881_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6881_, 0, v_a_6875_);
                    v___x_6880_ = v_reuseFailAlloc_6881_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6880_;
            }
            9 => {
                if v_isShared_6886_ == 0 {
                    v___x_6888_ = v___x_6885_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6889_, 0, v_a_6883_);
                    v___x_6888_ = v_reuseFailAlloc_6889_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6888_;
            }
            11 => {
                crate::leanh::lean_inc_ref(v___y_6895_);
                v___x_6915_ = l_Array_append___redArg(v___y_6895_, v___y_6914_);
                crate::leanh::lean_dec_ref(v___y_6914_);
                crate::leanh::lean_inc(v___y_6904_);
                crate::leanh::lean_inc(v___y_6909_);
                v___x_6916_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6916_, 0, v___y_6909_);
                crate::leanh::lean_ctor_set(v___x_6916_, 1, v___y_6904_);
                crate::leanh::lean_ctor_set(v___x_6916_, 2, v___x_6915_);
                if crate::leanh::lean_obj_tag(v___y_6900_) == 1 {
                    v_val_6917_ = crate::leanh::lean_ctor_get(v___y_6900_, 0);
                    crate::leanh::lean_inc(v_val_6917_);
                    crate::leanh::lean_dec_ref_known(v___y_6900_, 1);
                    v___x_6918_ = l_Lean_Elab_Command_elabElab___closed__8;
                    v___x_6919_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__1;
                    crate::leanh::lean_inc_n(v___y_6909_, 5);
                    v___x_6920_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6920_, 0, v___y_6909_);
                    crate::leanh::lean_ctor_set(v___x_6920_, 1, v___x_6919_);
                    v___x_6921_ = l_Lean_Elab_Command_elabElab___closed__9;
                    v___x_6922_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6922_, 0, v___y_6909_);
                    crate::leanh::lean_ctor_set(v___x_6922_, 1, v___x_6921_);
                    v___x_6923_ = l_Lean_Elab_Command_elabElabRulesAux___closed__11;
                    v___x_6924_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6924_, 0, v___y_6909_);
                    crate::leanh::lean_ctor_set(v___x_6924_, 1, v___x_6923_);
                    v___x_6925_ = l_Lean_Elab_Command_elabElabRules___lam__1___closed__3;
                    v___x_6926_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6926_, 0, v___y_6909_);
                    crate::leanh::lean_ctor_set(v___x_6926_, 1, v___x_6925_);
                    v___x_6927_ = l_Lean_Syntax_node5(
                        v___y_6909_,
                        v___x_6918_,
                        v___x_6920_,
                        v___x_6922_,
                        v___x_6924_,
                        v_val_6917_,
                        v___x_6926_,
                    );
                    v___x_6928_ = l_Array_mkArray1___redArg(v___x_6927_);
                    v___y_6800_ = v___y_6892_;
                    v___y_6801_ = v___y_6893_;
                    v___y_6802_ = v___y_6894_;
                    v___y_6803_ = v___y_6895_;
                    v___y_6804_ = v___y_6896_;
                    v___y_6805_ = v___y_6897_;
                    v___y_6806_ = v___y_6898_;
                    v___y_6807_ = v___y_6899_;
                    v___y_6808_ = v___x_6916_;
                    v___y_6809_ = v___y_6901_;
                    v___y_6810_ = v___y_6902_;
                    v___y_6811_ = v___y_6903_;
                    v___y_6812_ = v___y_6904_;
                    v___y_6813_ = v___y_6905_;
                    v___y_6814_ = v___y_6908_;
                    v___y_6815_ = v___y_6909_;
                    v___y_6816_ = v___y_6907_;
                    v___y_6817_ = v___y_6906_;
                    v___y_6818_ = v___y_6910_;
                    v___y_6819_ = v___y_6911_;
                    v___y_6820_ = v___y_6913_;
                    v___y_6821_ = v___y_6912_;
                    v___y_6822_ = v___x_6928_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6900_);
                    v___x_6929_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_6800_ = v___y_6892_;
                    v___y_6801_ = v___y_6893_;
                    v___y_6802_ = v___y_6894_;
                    v___y_6803_ = v___y_6895_;
                    v___y_6804_ = v___y_6896_;
                    v___y_6805_ = v___y_6897_;
                    v___y_6806_ = v___y_6898_;
                    v___y_6807_ = v___y_6899_;
                    v___y_6808_ = v___x_6916_;
                    v___y_6809_ = v___y_6901_;
                    v___y_6810_ = v___y_6902_;
                    v___y_6811_ = v___y_6903_;
                    v___y_6812_ = v___y_6904_;
                    v___y_6813_ = v___y_6905_;
                    v___y_6814_ = v___y_6908_;
                    v___y_6815_ = v___y_6909_;
                    v___y_6816_ = v___y_6907_;
                    v___y_6817_ = v___y_6906_;
                    v___y_6818_ = v___y_6910_;
                    v___y_6819_ = v___y_6911_;
                    v___y_6820_ = v___y_6913_;
                    v___y_6821_ = v___y_6912_;
                    v___y_6822_ = v___x_6929_;
                    state = 4;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc_ref(v___y_6934_);
                v___x_6955_ = l_Array_append___redArg(v___y_6934_, v___y_6954_);
                crate::leanh::lean_dec_ref(v___y_6954_);
                crate::leanh::lean_inc(v___y_6944_);
                crate::leanh::lean_inc(v___y_6949_);
                v___x_6956_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6956_, 0, v___y_6949_);
                crate::leanh::lean_ctor_set(v___x_6956_, 1, v___y_6944_);
                crate::leanh::lean_ctor_set(v___x_6956_, 2, v___x_6955_);
                v___x_6957_ = l_Lean_SourceInfo_fromRef(v___y_6931_, v___x_6747_);
                crate::leanh::lean_dec(v___y_6931_);
                crate::leanh::lean_inc_ref(v___y_6945_);
                v___x_6958_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6958_, 0, v___x_6957_);
                crate::leanh::lean_ctor_set(v___x_6958_, 1, v___y_6945_);
                if crate::leanh::lean_obj_tag(v___y_6942_) == 1 {
                    v_val_6959_ = crate::leanh::lean_ctor_get(v___y_6942_, 0);
                    crate::leanh::lean_inc(v_val_6959_);
                    crate::leanh::lean_dec_ref_known(v___y_6942_, 1);
                    v___x_6960_ = l_Lean_Elab_Command_elabElab___closed__11;
                    v___x_6961_ = l_Lean_Elab_Command_elabElabRulesAux___closed__7;
                    crate::leanh::lean_inc_n(v___y_6949_, 2);
                    v___x_6962_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6962_, 0, v___y_6949_);
                    crate::leanh::lean_ctor_set(v___x_6962_, 1, v___x_6961_);
                    v___x_6963_ =
                        l_Lean_Syntax_node2(v___y_6949_, v___x_6960_, v___x_6962_, v_val_6959_);
                    v___x_6964_ = l_Array_mkArray1___redArg(v___x_6963_);
                    v___y_6892_ = v___y_6932_;
                    v___y_6893_ = v___y_6933_;
                    v___y_6894_ = v___x_6956_;
                    v___y_6895_ = v___y_6934_;
                    v___y_6896_ = v___y_6935_;
                    v___y_6897_ = v___y_6936_;
                    v___y_6898_ = v___y_6937_;
                    v___y_6899_ = v___y_6938_;
                    v___y_6900_ = v___y_6939_;
                    v___y_6901_ = v___y_6940_;
                    v___y_6902_ = v___y_6941_;
                    v___y_6903_ = v___y_6943_;
                    v___y_6904_ = v___y_6944_;
                    v___y_6905_ = v___x_6958_;
                    v___y_6906_ = v___y_6948_;
                    v___y_6907_ = v___y_6947_;
                    v___y_6908_ = v___y_6946_;
                    v___y_6909_ = v___y_6949_;
                    v___y_6910_ = v___y_6950_;
                    v___y_6911_ = v___y_6951_;
                    v___y_6912_ = v___y_6953_;
                    v___y_6913_ = v___y_6952_;
                    v___y_6914_ = v___x_6964_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6942_);
                    v___x_6965_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_6892_ = v___y_6932_;
                    v___y_6893_ = v___y_6933_;
                    v___y_6894_ = v___x_6956_;
                    v___y_6895_ = v___y_6934_;
                    v___y_6896_ = v___y_6935_;
                    v___y_6897_ = v___y_6936_;
                    v___y_6898_ = v___y_6937_;
                    v___y_6899_ = v___y_6938_;
                    v___y_6900_ = v___y_6939_;
                    v___y_6901_ = v___y_6940_;
                    v___y_6902_ = v___y_6941_;
                    v___y_6903_ = v___y_6943_;
                    v___y_6904_ = v___y_6944_;
                    v___y_6905_ = v___x_6958_;
                    v___y_6906_ = v___y_6948_;
                    v___y_6907_ = v___y_6947_;
                    v___y_6908_ = v___y_6946_;
                    v___y_6909_ = v___y_6949_;
                    v___y_6910_ = v___y_6950_;
                    v___y_6911_ = v___y_6951_;
                    v___y_6912_ = v___y_6953_;
                    v___y_6913_ = v___y_6952_;
                    v___y_6914_ = v___x_6965_;
                    state = 11;
                    continue;
                }
            }
            13 => {
                crate::leanh::lean_inc_ref(v___y_6970_);
                v___x_6991_ = l_Array_append___redArg(v___y_6970_, v___y_6990_);
                crate::leanh::lean_dec_ref(v___y_6990_);
                crate::leanh::lean_inc(v___y_6980_);
                crate::leanh::lean_inc(v___y_6984_);
                v___x_6992_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6992_, 0, v___y_6984_);
                crate::leanh::lean_ctor_set(v___x_6992_, 1, v___y_6980_);
                crate::leanh::lean_ctor_set(v___x_6992_, 2, v___x_6991_);
                if crate::leanh::lean_obj_tag(v___y_6985_) == 1 {
                    v_val_6993_ = crate::leanh::lean_ctor_get(v___y_6985_, 0);
                    crate::leanh::lean_inc(v_val_6993_);
                    crate::leanh::lean_dec_ref_known(v___y_6985_, 1);
                    v___x_6994_ = l_Lean_Elab_Command_elabElabRulesAux___closed__0;
                    crate::leanh::lean_inc_ref(v___y_6972_);
                    v___x_6995_ =
                        l_Lean_Name_mkStr4(v___x_6704_, v___x_6705_, v___y_6972_, v___x_6994_);
                    v___x_6996_ = l_Lean_Elab_Command_elabElabRulesAux___closed__1;
                    crate::leanh::lean_inc_n(v___y_6984_, 4);
                    v___x_6997_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6997_, 0, v___y_6984_);
                    crate::leanh::lean_ctor_set(v___x_6997_, 1, v___x_6996_);
                    crate::leanh::lean_inc_ref(v___y_6970_);
                    v___x_6998_ = l_Array_append___redArg(v___y_6970_, v_val_6993_);
                    crate::leanh::lean_dec(v_val_6993_);
                    crate::leanh::lean_inc(v___y_6980_);
                    v___x_6999_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6999_, 0, v___y_6984_);
                    crate::leanh::lean_ctor_set(v___x_6999_, 1, v___y_6980_);
                    crate::leanh::lean_ctor_set(v___x_6999_, 2, v___x_6998_);
                    v___x_7000_ = l_Lean_Elab_Command_elabElabRulesAux___closed__3;
                    v___x_7001_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7001_, 0, v___y_6984_);
                    crate::leanh::lean_ctor_set(v___x_7001_, 1, v___x_7000_);
                    v___x_7002_ = l_Lean_Syntax_node3(
                        v___y_6984_,
                        v___x_6995_,
                        v___x_6997_,
                        v___x_6999_,
                        v___x_7001_,
                    );
                    v___x_7003_ = l_Array_mkArray1___redArg(v___x_7002_);
                    v___y_6931_ = v___y_6967_;
                    v___y_6932_ = v___y_6968_;
                    v___y_6933_ = v___y_6969_;
                    v___y_6934_ = v___y_6970_;
                    v___y_6935_ = v___y_6971_;
                    v___y_6936_ = v___y_6972_;
                    v___y_6937_ = v___y_6973_;
                    v___y_6938_ = v___y_6974_;
                    v___y_6939_ = v___y_6975_;
                    v___y_6940_ = v___y_6976_;
                    v___y_6941_ = v___y_6977_;
                    v___y_6942_ = v___y_6978_;
                    v___y_6943_ = v___y_6979_;
                    v___y_6944_ = v___y_6980_;
                    v___y_6945_ = v___y_6981_;
                    v___y_6946_ = v___y_6983_;
                    v___y_6947_ = v___y_6982_;
                    v___y_6948_ = v___x_6992_;
                    v___y_6949_ = v___y_6984_;
                    v___y_6950_ = v___y_6986_;
                    v___y_6951_ = v___y_6987_;
                    v___y_6952_ = v___y_6989_;
                    v___y_6953_ = v___y_6988_;
                    v___y_6954_ = v___x_7003_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___y_6985_);
                    v___x_7004_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_6931_ = v___y_6967_;
                    v___y_6932_ = v___y_6968_;
                    v___y_6933_ = v___y_6969_;
                    v___y_6934_ = v___y_6970_;
                    v___y_6935_ = v___y_6971_;
                    v___y_6936_ = v___y_6972_;
                    v___y_6937_ = v___y_6973_;
                    v___y_6938_ = v___y_6974_;
                    v___y_6939_ = v___y_6975_;
                    v___y_6940_ = v___y_6976_;
                    v___y_6941_ = v___y_6977_;
                    v___y_6942_ = v___y_6978_;
                    v___y_6943_ = v___y_6979_;
                    v___y_6944_ = v___y_6980_;
                    v___y_6945_ = v___y_6981_;
                    v___y_6946_ = v___y_6983_;
                    v___y_6947_ = v___y_6982_;
                    v___y_6948_ = v___x_6992_;
                    v___y_6949_ = v___y_6984_;
                    v___y_6950_ = v___y_6986_;
                    v___y_6951_ = v___y_6987_;
                    v___y_6952_ = v___y_6989_;
                    v___y_6953_ = v___y_6988_;
                    v___y_6954_ = v___x_7004_;
                    state = 12;
                    continue;
                }
            }
            14 => {
                v___x_7025_ = l_Lean_Elab_Command_elabElab___closed__12;
                v___x_7026_ = l_Lean_Elab_Command_elabElab___closed__13;
                v___x_7027_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__9;
                v___x_7028_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElabRulesAux_spec__5___closed__7);
                if crate::leanh::lean_obj_tag(v___y_7019_) == 1 {
                    v_val_7029_ = crate::leanh::lean_ctor_get(v___y_7019_, 0);
                    crate::leanh::lean_inc(v_val_7029_);
                    v___x_7030_ = l_Array_mkArray1___redArg(v_val_7029_);
                    v___y_6967_ = v___y_7006_;
                    v___y_6968_ = v___y_7007_;
                    v___y_6969_ = v___y_7008_;
                    v___y_6970_ = v___x_7028_;
                    v___y_6971_ = v___y_7009_;
                    v___y_6972_ = v___y_7010_;
                    v___y_6973_ = v___y_7011_;
                    v___y_6974_ = v___y_7012_;
                    v___y_6975_ = v___y_7013_;
                    v___y_6976_ = v___y_7014_;
                    v___y_6977_ = v___y_7015_;
                    v___y_6978_ = v___y_7016_;
                    v___y_6979_ = v___y_7017_;
                    v___y_6980_ = v___x_7027_;
                    v___y_6981_ = v___x_7025_;
                    v___y_6982_ = v___y_7020_;
                    v___y_6983_ = v___y_7019_;
                    v___y_6984_ = v___y_7018_;
                    v___y_6985_ = v___y_7022_;
                    v___y_6986_ = v___y_7021_;
                    v___y_6987_ = v___x_7026_;
                    v___y_6988_ = v___y_7024_;
                    v___y_6989_ = v___y_7023_;
                    v___y_6990_ = v___x_7030_;
                    state = 13;
                    continue;
                } else {
                    v___x_7031_ = l_Lean_Elab_Command_elabElabRulesAux___closed__32;
                    v___y_6967_ = v___y_7006_;
                    v___y_6968_ = v___y_7007_;
                    v___y_6969_ = v___y_7008_;
                    v___y_6970_ = v___x_7028_;
                    v___y_6971_ = v___y_7009_;
                    v___y_6972_ = v___y_7010_;
                    v___y_6973_ = v___y_7011_;
                    v___y_6974_ = v___y_7012_;
                    v___y_6975_ = v___y_7013_;
                    v___y_6976_ = v___y_7014_;
                    v___y_6977_ = v___y_7015_;
                    v___y_6978_ = v___y_7016_;
                    v___y_6979_ = v___y_7017_;
                    v___y_6980_ = v___x_7027_;
                    v___y_6981_ = v___x_7025_;
                    v___y_6982_ = v___y_7020_;
                    v___y_6983_ = v___y_7019_;
                    v___y_6984_ = v___y_7018_;
                    v___y_6985_ = v___y_7022_;
                    v___y_6986_ = v___y_7021_;
                    v___y_6987_ = v___x_7026_;
                    v___y_6988_ = v___y_7024_;
                    v___y_6989_ = v___y_7023_;
                    v___y_6990_ = v___x_7031_;
                    state = 13;
                    continue;
                }
            }
            15 => {
                v___x_7049_ = crate::leanh::lean_alloc_closure(
                    l_Lean_evalOptPrio___boxed as *mut core::ffi::c_void,
                    3,
                    1,
                );
                crate::leanh::lean_closure_set(v___x_7049_, 0, v___y_7038_);
                v___x_7050_ =
                    l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(
                        v___x_7049_,
                        v___y_7047_,
                        v___y_7048_,
                    );
                if crate::leanh::lean_obj_tag(v___x_7050_) == 0 {
                    v_a_7051_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                    crate::leanh::lean_inc(v_a_7051_);
                    crate::leanh::lean_dec_ref_known(v___x_7050_, 1);
                    v_args_7052_ = l_Lean_Syntax_getArgs(v___y_7034_);
                    crate::leanh::lean_dec(v___y_7034_);
                    v_sz_7053_ = lean_array_size(v_args_7052_);
                    v___x_7054_ = 0usize;
                    v___x_7055_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Command_elabElab_spec__1(v_sz_7053_, v___x_7054_, v_args_7052_, v___y_7047_, v___y_7048_);
                    if crate::leanh::lean_obj_tag(v___x_7055_) == 0 {
                        v_a_7056_ = crate::leanh::lean_ctor_get(v___x_7055_, 0);
                        crate::leanh::lean_inc(v_a_7056_);
                        crate::leanh::lean_dec_ref_known(v___x_7055_, 1);
                        v___x_7057_ = l_Array_unzip___redArg(v_a_7056_);
                        crate::leanh::lean_dec(v_a_7056_);
                        v_fst_7058_ = crate::leanh::lean_ctor_get(v___x_7057_, 0);
                        crate::leanh::lean_inc(v_fst_7058_);
                        v_snd_7059_ = crate::leanh::lean_ctor_get(v___x_7057_, 1);
                        crate::leanh::lean_inc(v_snd_7059_);
                        crate::leanh::lean_dec_ref(v___x_7057_);
                        v___x_7060_ = l_Lean_Elab_Command_getRef___redArg(v___y_7047_);
                        if crate::leanh::lean_obj_tag(v___x_7060_) == 0 {
                            v_a_7061_ = crate::leanh::lean_ctor_get(v___x_7060_, 0);
                            crate::leanh::lean_inc(v_a_7061_);
                            crate::leanh::lean_dec_ref_known(v___x_7060_, 1);
                            v___x_7062_ =
                                l_Lean_Elab_Command_getCurrMacroScope___redArg(v___y_7047_);
                            if crate::leanh::lean_obj_tag(v___x_7062_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7062_, 1);
                                v_quotContext_x3f_7063_ =
                                    crate::leanh::lean_ctor_get(v___y_7047_, 5);
                                v___x_7064_ = l_Lean_Syntax_getArg(v___y_7040_, v___y_7035_);
                                crate::leanh::lean_dec(v___y_7040_);
                                v___x_7065_ = 0;
                                v___x_7066_ = l_Lean_SourceInfo_fromRef(v_a_7061_, v___x_7065_);
                                crate::leanh::lean_dec(v_a_7061_);
                                if crate::leanh::lean_obj_tag(v_quotContext_x3f_7063_) == 0 {
                                    v___x_7067_ = l_Lean_getMainModule___at___00Lean_Elab_Command_elabElabRulesAux_spec__1___redArg(v___y_7048_);
                                    crate::leanh::lean_dec_ref(v___x_7067_);
                                    v___y_7006_ = v___y_7033_;
                                    v___y_7007_ = v___x_7065_;
                                    v___y_7008_ = v___y_7036_;
                                    v___y_7009_ = v___x_7064_;
                                    v___y_7010_ = v___y_7037_;
                                    v___y_7011_ = v___y_7039_;
                                    v___y_7012_ = v___y_7048_;
                                    v___y_7013_ = v___y_7041_;
                                    v___y_7014_ = v___y_7047_;
                                    v___y_7015_ = v_expectedType_x3f_7046_;
                                    v___y_7016_ = v___y_7042_;
                                    v___y_7017_ = v_a_7051_;
                                    v___y_7018_ = v___x_7066_;
                                    v___y_7019_ = v___y_7043_;
                                    v___y_7020_ = v_fst_7058_;
                                    v___y_7021_ = v___x_7054_;
                                    v___y_7022_ = v___y_7044_;
                                    v___y_7023_ = v_snd_7059_;
                                    v___y_7024_ = v___y_7045_;
                                    state = 14;
                                    continue;
                                } else {
                                    v___y_7006_ = v___y_7033_;
                                    v___y_7007_ = v___x_7065_;
                                    v___y_7008_ = v___y_7036_;
                                    v___y_7009_ = v___x_7064_;
                                    v___y_7010_ = v___y_7037_;
                                    v___y_7011_ = v___y_7039_;
                                    v___y_7012_ = v___y_7048_;
                                    v___y_7013_ = v___y_7041_;
                                    v___y_7014_ = v___y_7047_;
                                    v___y_7015_ = v_expectedType_x3f_7046_;
                                    v___y_7016_ = v___y_7042_;
                                    v___y_7017_ = v_a_7051_;
                                    v___y_7018_ = v___x_7066_;
                                    v___y_7019_ = v___y_7043_;
                                    v___y_7020_ = v_fst_7058_;
                                    v___y_7021_ = v___x_7054_;
                                    v___y_7022_ = v___y_7044_;
                                    v___y_7023_ = v_snd_7059_;
                                    v___y_7024_ = v___y_7045_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7061_);
                                crate::leanh::lean_dec(v_snd_7059_);
                                crate::leanh::lean_dec(v_fst_7058_);
                                crate::leanh::lean_dec(v_a_7051_);
                                crate::leanh::lean_dec(v_expectedType_x3f_7046_);
                                crate::leanh::lean_dec(v___y_7045_);
                                crate::leanh::lean_dec(v___y_7044_);
                                crate::leanh::lean_dec(v___y_7043_);
                                crate::leanh::lean_dec(v___y_7042_);
                                crate::leanh::lean_dec(v___y_7041_);
                                crate::leanh::lean_dec(v___y_7040_);
                                crate::leanh::lean_dec(v___y_7039_);
                                crate::leanh::lean_dec(v___y_7033_);
                                v_a_7068_ = crate::leanh::lean_ctor_get(v___x_7062_, 0);
                                v_isSharedCheck_7075_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7062_)) as u8;
                                if v_isSharedCheck_7075_ == 0 {
                                    v___x_7070_ = v___x_7062_;
                                    v_isShared_7071_ = v_isSharedCheck_7075_;
                                    state = 16;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7068_);
                                    crate::leanh::lean_dec(v___x_7062_);
                                    v___x_7070_ = crate::leanh::lean_box(0);
                                    v_isShared_7071_ = v_isSharedCheck_7075_;
                                    state = 16;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_snd_7059_);
                            crate::leanh::lean_dec(v_fst_7058_);
                            crate::leanh::lean_dec(v_a_7051_);
                            crate::leanh::lean_dec(v_expectedType_x3f_7046_);
                            crate::leanh::lean_dec(v___y_7045_);
                            crate::leanh::lean_dec(v___y_7044_);
                            crate::leanh::lean_dec(v___y_7043_);
                            crate::leanh::lean_dec(v___y_7042_);
                            crate::leanh::lean_dec(v___y_7041_);
                            crate::leanh::lean_dec(v___y_7040_);
                            crate::leanh::lean_dec(v___y_7039_);
                            crate::leanh::lean_dec(v___y_7033_);
                            v_a_7076_ = crate::leanh::lean_ctor_get(v___x_7060_, 0);
                            v_isSharedCheck_7083_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7060_)) as u8;
                            if v_isSharedCheck_7083_ == 0 {
                                v___x_7078_ = v___x_7060_;
                                v_isShared_7079_ = v_isSharedCheck_7083_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7076_);
                                crate::leanh::lean_dec(v___x_7060_);
                                v___x_7078_ = crate::leanh::lean_box(0);
                                v_isShared_7079_ = v_isSharedCheck_7083_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_7051_);
                        crate::leanh::lean_dec(v_expectedType_x3f_7046_);
                        crate::leanh::lean_dec(v___y_7045_);
                        crate::leanh::lean_dec(v___y_7044_);
                        crate::leanh::lean_dec(v___y_7043_);
                        crate::leanh::lean_dec(v___y_7042_);
                        crate::leanh::lean_dec(v___y_7041_);
                        crate::leanh::lean_dec(v___y_7040_);
                        crate::leanh::lean_dec(v___y_7039_);
                        crate::leanh::lean_dec(v___y_7033_);
                        v_a_7084_ = crate::leanh::lean_ctor_get(v___x_7055_, 0);
                        v_isSharedCheck_7091_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7055_)) as u8;
                        if v_isSharedCheck_7091_ == 0 {
                            v___x_7086_ = v___x_7055_;
                            v_isShared_7087_ = v_isSharedCheck_7091_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7084_);
                            crate::leanh::lean_dec(v___x_7055_);
                            v___x_7086_ = crate::leanh::lean_box(0);
                            v_isShared_7087_ = v_isSharedCheck_7091_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_expectedType_x3f_7046_);
                    crate::leanh::lean_dec(v___y_7045_);
                    crate::leanh::lean_dec(v___y_7044_);
                    crate::leanh::lean_dec(v___y_7043_);
                    crate::leanh::lean_dec(v___y_7042_);
                    crate::leanh::lean_dec(v___y_7041_);
                    crate::leanh::lean_dec(v___y_7040_);
                    crate::leanh::lean_dec(v___y_7039_);
                    crate::leanh::lean_dec(v___y_7034_);
                    crate::leanh::lean_dec(v___y_7033_);
                    v_a_7092_ = crate::leanh::lean_ctor_get(v___x_7050_, 0);
                    v_isSharedCheck_7099_ = (!crate::leanh::lean_is_exclusive(v___x_7050_)) as u8;
                    if v_isSharedCheck_7099_ == 0 {
                        v___x_7094_ = v___x_7050_;
                        v_isShared_7095_ = v_isSharedCheck_7099_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7092_);
                        crate::leanh::lean_dec(v___x_7050_);
                        v___x_7094_ = crate::leanh::lean_box(0);
                        v_isShared_7095_ = v_isSharedCheck_7099_;
                        state = 22;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_7071_ == 0 {
                    v___x_7073_ = v___x_7070_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_7074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7074_, 0, v_a_7068_);
                    v___x_7073_ = v_reuseFailAlloc_7074_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_7073_;
            }
            18 => {
                if v_isShared_7079_ == 0 {
                    v___x_7081_ = v___x_7078_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7082_, 0, v_a_7076_);
                    v___x_7081_ = v_reuseFailAlloc_7082_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_7081_;
            }
            20 => {
                if v_isShared_7087_ == 0 {
                    v___x_7089_ = v___x_7086_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7090_, 0, v_a_7084_);
                    v___x_7089_ = v_reuseFailAlloc_7090_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7089_;
            }
            22 => {
                if v_isShared_7095_ == 0 {
                    v___x_7097_ = v___x_7094_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7098_, 0, v_a_7092_);
                    v___x_7097_ = v_reuseFailAlloc_7098_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7097_;
            }
            24 => {
                v___x_7115_ = crate::leanh::lean_unsigned_to_nat(8);
                v___x_7116_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7115_);
                v___x_7117_ = l_Lean_Elab_Command_elabElab___closed__15;
                crate::leanh::lean_inc(v___x_7116_);
                v___x_7118_ = l_Lean_Syntax_isOfKind(v___x_7116_, v___x_7117_);
                if v___x_7118_ == 0 {
                    crate::leanh::lean_dec(v___x_7116_);
                    crate::leanh::lean_dec(v_prio_x3f_7112_);
                    crate::leanh::lean_dec(v___y_7109_);
                    crate::leanh::lean_dec(v___y_7108_);
                    crate::leanh::lean_dec(v___y_7107_);
                    crate::leanh::lean_dec(v___y_7104_);
                    crate::leanh::lean_dec(v___y_7102_);
                    crate::leanh::lean_dec(v___y_7101_);
                    crate::leanh::lean_dec(v_x_6700_);
                    v___x_7119_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_7119_;
                } else {
                    v___x_7120_ = crate::leanh::lean_unsigned_to_nat(7);
                    v___x_7121_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7120_);
                    crate::leanh::lean_dec(v_x_6700_);
                    v___x_7122_ = l_Lean_Syntax_getArg(v___x_7116_, v___y_7111_);
                    v___x_7123_ = l_Lean_Syntax_getArg(v___x_7116_, v___y_7103_);
                    v___x_7124_ = l_Lean_Syntax_isNone(v___x_7123_);
                    if v___x_7124_ == 0 {
                        crate::leanh::lean_inc(v___x_7123_);
                        v___x_7125_ = l_Lean_Syntax_matchesNull(v___x_7123_, v___y_7103_);
                        if v___x_7125_ == 0 {
                            crate::leanh::lean_dec(v___x_7123_);
                            crate::leanh::lean_dec(v___x_7122_);
                            crate::leanh::lean_dec(v___x_7121_);
                            crate::leanh::lean_dec(v___x_7116_);
                            crate::leanh::lean_dec(v_prio_x3f_7112_);
                            crate::leanh::lean_dec(v___y_7109_);
                            crate::leanh::lean_dec(v___y_7108_);
                            crate::leanh::lean_dec(v___y_7107_);
                            crate::leanh::lean_dec(v___y_7104_);
                            crate::leanh::lean_dec(v___y_7102_);
                            crate::leanh::lean_dec(v___y_7101_);
                            v___x_7126_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_7126_;
                        } else {
                            v_expectedType_x3f_7127_ =
                                l_Lean_Syntax_getArg(v___x_7123_, v___y_7111_);
                            crate::leanh::lean_dec(v___x_7123_);
                            v___x_7128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7128_, 0, v_expectedType_x3f_7127_);
                            v___y_7033_ = v___y_7101_;
                            v___y_7034_ = v___x_7121_;
                            v___y_7035_ = v___y_7105_;
                            v___y_7036_ = v___y_7106_;
                            v___y_7037_ = v___y_7110_;
                            v___y_7038_ = v_prio_x3f_7112_;
                            v___y_7039_ = v___x_7122_;
                            v___y_7040_ = v___x_7116_;
                            v___y_7041_ = v___y_7102_;
                            v___y_7042_ = v___y_7104_;
                            v___y_7043_ = v___y_7107_;
                            v___y_7044_ = v___y_7108_;
                            v___y_7045_ = v___y_7109_;
                            v_expectedType_x3f_7046_ = v___x_7128_;
                            v___y_7047_ = v___y_7113_;
                            v___y_7048_ = v___y_7114_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7123_);
                        v___x_7129_ = crate::leanh::lean_box(0);
                        v___y_7033_ = v___y_7101_;
                        v___y_7034_ = v___x_7121_;
                        v___y_7035_ = v___y_7105_;
                        v___y_7036_ = v___y_7106_;
                        v___y_7037_ = v___y_7110_;
                        v___y_7038_ = v_prio_x3f_7112_;
                        v___y_7039_ = v___x_7122_;
                        v___y_7040_ = v___x_7116_;
                        v___y_7041_ = v___y_7102_;
                        v___y_7042_ = v___y_7104_;
                        v___y_7043_ = v___y_7107_;
                        v___y_7044_ = v___y_7108_;
                        v___y_7045_ = v___y_7109_;
                        v_expectedType_x3f_7046_ = v___x_7129_;
                        v___y_7047_ = v___y_7113_;
                        v___y_7048_ = v___y_7114_;
                        state = 15;
                        continue;
                    }
                }
            }
            25 => {
                v___x_7145_ = crate::leanh::lean_unsigned_to_nat(6);
                v___x_7146_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7145_);
                v___x_7147_ = l_Lean_Syntax_isNone(v___x_7146_);
                if v___x_7147_ == 0 {
                    crate::leanh::lean_inc(v___x_7146_);
                    v___x_7148_ = l_Lean_Syntax_matchesNull(v___x_7146_, v___y_7139_);
                    if v___x_7148_ == 0 {
                        crate::leanh::lean_dec(v___x_7146_);
                        crate::leanh::lean_dec(v_name_x3f_7142_);
                        crate::leanh::lean_dec(v___y_7141_);
                        crate::leanh::lean_dec(v___y_7138_);
                        crate::leanh::lean_dec(v___y_7136_);
                        crate::leanh::lean_dec(v___y_7132_);
                        crate::leanh::lean_dec(v___y_7131_);
                        crate::leanh::lean_dec(v_x_6700_);
                        v___x_7149_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_7149_;
                    } else {
                        v___x_7150_ = l_Lean_Syntax_getArg(v___x_7146_, v___x_6749_);
                        crate::leanh::lean_dec(v___x_7146_);
                        v___x_7151_ = l_Lean_Elab_Command_elabElab___closed__5;
                        crate::leanh::lean_inc(v___x_7150_);
                        v___x_7152_ = l_Lean_Syntax_isOfKind(v___x_7150_, v___x_7151_);
                        if v___x_7152_ == 0 {
                            crate::leanh::lean_dec(v___x_7150_);
                            crate::leanh::lean_dec(v_name_x3f_7142_);
                            crate::leanh::lean_dec(v___y_7141_);
                            crate::leanh::lean_dec(v___y_7138_);
                            crate::leanh::lean_dec(v___y_7136_);
                            crate::leanh::lean_dec(v___y_7132_);
                            crate::leanh::lean_dec(v___y_7131_);
                            crate::leanh::lean_dec(v_x_6700_);
                            v___x_7153_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_7153_;
                        } else {
                            v_prio_x3f_7154_ = l_Lean_Syntax_getArg(v___x_7150_, v___y_7137_);
                            crate::leanh::lean_dec(v___x_7150_);
                            v___x_7155_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7155_, 0, v_prio_x3f_7154_);
                            v___y_7101_ = v___y_7131_;
                            v___y_7102_ = v_name_x3f_7142_;
                            v___y_7103_ = v___y_7133_;
                            v___y_7104_ = v___y_7132_;
                            v___y_7105_ = v___y_7134_;
                            v___y_7106_ = v___y_7135_;
                            v___y_7107_ = v___y_7136_;
                            v___y_7108_ = v___y_7138_;
                            v___y_7109_ = v___y_7141_;
                            v___y_7110_ = v___y_7140_;
                            v___y_7111_ = v___y_7139_;
                            v_prio_x3f_7112_ = v___x_7155_;
                            v___y_7113_ = v___y_7143_;
                            v___y_7114_ = v___y_7144_;
                            state = 24;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7146_);
                    v___x_7156_ = crate::leanh::lean_box(0);
                    v___y_7101_ = v___y_7131_;
                    v___y_7102_ = v_name_x3f_7142_;
                    v___y_7103_ = v___y_7133_;
                    v___y_7104_ = v___y_7132_;
                    v___y_7105_ = v___y_7134_;
                    v___y_7106_ = v___y_7135_;
                    v___y_7107_ = v___y_7136_;
                    v___y_7108_ = v___y_7138_;
                    v___y_7109_ = v___y_7141_;
                    v___y_7110_ = v___y_7140_;
                    v___y_7111_ = v___y_7139_;
                    v_prio_x3f_7112_ = v___x_7156_;
                    v___y_7113_ = v___y_7143_;
                    v___y_7114_ = v___y_7144_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                v___x_7171_ = crate::leanh::lean_unsigned_to_nat(5);
                v___x_7172_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7171_);
                v___x_7173_ = l_Lean_Syntax_isNone(v___x_7172_);
                if v___x_7173_ == 0 {
                    crate::leanh::lean_inc(v___x_7172_);
                    v___x_7174_ = l_Lean_Syntax_matchesNull(v___x_7172_, v___y_7167_);
                    if v___x_7174_ == 0 {
                        crate::leanh::lean_dec(v___x_7172_);
                        crate::leanh::lean_dec(v_prec_x3f_7168_);
                        crate::leanh::lean_dec(v___y_7165_);
                        crate::leanh::lean_dec(v___y_7164_);
                        crate::leanh::lean_dec(v___y_7162_);
                        crate::leanh::lean_dec(v___y_7158_);
                        crate::leanh::lean_dec(v_x_6700_);
                        v___x_7175_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_7175_;
                    } else {
                        v___x_7176_ = l_Lean_Syntax_getArg(v___x_7172_, v___x_6749_);
                        crate::leanh::lean_dec(v___x_7172_);
                        v___x_7177_ = l_Lean_Elab_Command_elabElab___closed__8;
                        crate::leanh::lean_inc(v___x_7176_);
                        v___x_7178_ = l_Lean_Syntax_isOfKind(v___x_7176_, v___x_7177_);
                        if v___x_7178_ == 0 {
                            crate::leanh::lean_dec(v___x_7176_);
                            crate::leanh::lean_dec(v_prec_x3f_7168_);
                            crate::leanh::lean_dec(v___y_7165_);
                            crate::leanh::lean_dec(v___y_7164_);
                            crate::leanh::lean_dec(v___y_7162_);
                            crate::leanh::lean_dec(v___y_7158_);
                            crate::leanh::lean_dec(v_x_6700_);
                            v___x_7179_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_7179_;
                        } else {
                            v_name_x3f_7180_ = l_Lean_Syntax_getArg(v___x_7176_, v___y_7163_);
                            crate::leanh::lean_dec(v___x_7176_);
                            v___x_7181_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7181_, 0, v_name_x3f_7180_);
                            v___y_7131_ = v___y_7158_;
                            v___y_7132_ = v_prec_x3f_7168_;
                            v___y_7133_ = v___y_7159_;
                            v___y_7134_ = v___y_7160_;
                            v___y_7135_ = v___y_7161_;
                            v___y_7136_ = v___y_7162_;
                            v___y_7137_ = v___y_7163_;
                            v___y_7138_ = v___y_7164_;
                            v___y_7139_ = v___y_7167_;
                            v___y_7140_ = v___y_7166_;
                            v___y_7141_ = v___y_7165_;
                            v_name_x3f_7142_ = v___x_7181_;
                            v___y_7143_ = v___y_7169_;
                            v___y_7144_ = v___y_7170_;
                            state = 25;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7172_);
                    v___x_7182_ = crate::leanh::lean_box(0);
                    v___y_7131_ = v___y_7158_;
                    v___y_7132_ = v_prec_x3f_7168_;
                    v___y_7133_ = v___y_7159_;
                    v___y_7134_ = v___y_7160_;
                    v___y_7135_ = v___y_7161_;
                    v___y_7136_ = v___y_7162_;
                    v___y_7137_ = v___y_7163_;
                    v___y_7138_ = v___y_7164_;
                    v___y_7139_ = v___y_7167_;
                    v___y_7140_ = v___y_7166_;
                    v___y_7141_ = v___y_7165_;
                    v_name_x3f_7142_ = v___x_7182_;
                    v___y_7143_ = v___y_7169_;
                    v___y_7144_ = v___y_7170_;
                    state = 25;
                    continue;
                }
            }
            27 => {
                v___x_7189_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_7190_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7189_);
                v___x_7191_ = l_Lean_Elab_Command_elabElabRulesAux___lam__0___closed__2;
                v___x_7192_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__4;
                crate::leanh::lean_inc(v___x_7190_);
                v___x_7193_ = l_Lean_Syntax_isOfKind(v___x_7190_, v___x_7192_);
                if v___x_7193_ == 0 {
                    crate::leanh::lean_dec(v___x_7190_);
                    crate::leanh::lean_dec(v_attrs_x3f_7186_);
                    crate::leanh::lean_dec(v___y_7184_);
                    crate::leanh::lean_dec(v_x_6700_);
                    v___x_7194_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                    return v___x_7194_;
                } else {
                    v___x_7195_ = crate::leanh::lean_unsigned_to_nat(3);
                    v_tk_7196_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7195_);
                    v___x_7197_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_7198_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7197_);
                    v___x_7199_ = l_Lean_Syntax_isNone(v___x_7198_);
                    if v___x_7199_ == 0 {
                        crate::leanh::lean_inc(v___x_7198_);
                        v___x_7200_ = l_Lean_Syntax_matchesNull(v___x_7198_, v___y_7185_);
                        if v___x_7200_ == 0 {
                            crate::leanh::lean_dec(v___x_7198_);
                            crate::leanh::lean_dec(v_tk_7196_);
                            crate::leanh::lean_dec(v___x_7190_);
                            crate::leanh::lean_dec(v_attrs_x3f_7186_);
                            crate::leanh::lean_dec(v___y_7184_);
                            crate::leanh::lean_dec(v_x_6700_);
                            v___x_7201_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_7201_;
                        } else {
                            v___x_7202_ = l_Lean_Syntax_getArg(v___x_7198_, v___x_6749_);
                            crate::leanh::lean_dec(v___x_7198_);
                            v___x_7203_ = l_Lean_Elab_Command_elabElab___closed__11;
                            crate::leanh::lean_inc(v___x_7202_);
                            v___x_7204_ = l_Lean_Syntax_isOfKind(v___x_7202_, v___x_7203_);
                            if v___x_7204_ == 0 {
                                crate::leanh::lean_dec(v___x_7202_);
                                crate::leanh::lean_dec(v_tk_7196_);
                                crate::leanh::lean_dec(v___x_7190_);
                                crate::leanh::lean_dec(v_attrs_x3f_7186_);
                                crate::leanh::lean_dec(v___y_7184_);
                                crate::leanh::lean_dec(v_x_6700_);
                                v___x_7205_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                                return v___x_7205_;
                            } else {
                                v_prec_x3f_7206_ = l_Lean_Syntax_getArg(v___x_7202_, v___y_7185_);
                                crate::leanh::lean_dec(v___x_7202_);
                                v___x_7207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_7207_, 0, v_prec_x3f_7206_);
                                v___y_7158_ = v_tk_7196_;
                                v___y_7159_ = v___x_7189_;
                                v___y_7160_ = v___x_7197_;
                                v___y_7161_ = v___x_7192_;
                                v___y_7162_ = v___y_7184_;
                                v___y_7163_ = v___x_7195_;
                                v___y_7164_ = v_attrs_x3f_7186_;
                                v___y_7165_ = v___x_7190_;
                                v___y_7166_ = v___x_7191_;
                                v___y_7167_ = v___y_7185_;
                                v_prec_x3f_7168_ = v___x_7207_;
                                v___y_7169_ = v___y_7187_;
                                v___y_7170_ = v___y_7188_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_7198_);
                        v___x_7208_ = crate::leanh::lean_box(0);
                        v___y_7158_ = v_tk_7196_;
                        v___y_7159_ = v___x_7189_;
                        v___y_7160_ = v___x_7197_;
                        v___y_7161_ = v___x_7192_;
                        v___y_7162_ = v___y_7184_;
                        v___y_7163_ = v___x_7195_;
                        v___y_7164_ = v_attrs_x3f_7186_;
                        v___y_7165_ = v___x_7190_;
                        v___y_7166_ = v___x_7191_;
                        v___y_7167_ = v___y_7185_;
                        v_prec_x3f_7168_ = v___x_7208_;
                        v___y_7169_ = v___y_7187_;
                        v___y_7170_ = v___y_7188_;
                        state = 26;
                        continue;
                    }
                }
            }
            28 => {
                v___x_7213_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_7214_ = l_Lean_Syntax_getArg(v_x_6700_, v___x_7213_);
                v___x_7215_ = l_Lean_Syntax_isNone(v___x_7214_);
                if v___x_7215_ == 0 {
                    crate::leanh::lean_inc(v___x_7214_);
                    v___x_7216_ = l_Lean_Syntax_matchesNull(v___x_7214_, v___x_7213_);
                    if v___x_7216_ == 0 {
                        crate::leanh::lean_dec(v___x_7214_);
                        crate::leanh::lean_dec(v_doc_x3f_7210_);
                        crate::leanh::lean_dec(v_x_6700_);
                        v___x_7217_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                        return v___x_7217_;
                    } else {
                        v___x_7218_ = l_Lean_Syntax_getArg(v___x_7214_, v___x_6749_);
                        crate::leanh::lean_dec(v___x_7214_);
                        v___x_7219_ = l_Lean_Elab_Command_elabElabRules___lam__2___closed__5;
                        crate::leanh::lean_inc(v___x_7218_);
                        v___x_7220_ = l_Lean_Syntax_isOfKind(v___x_7218_, v___x_7219_);
                        if v___x_7220_ == 0 {
                            crate::leanh::lean_dec(v___x_7218_);
                            crate::leanh::lean_dec(v_doc_x3f_7210_);
                            crate::leanh::lean_dec(v_x_6700_);
                            v___x_7221_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabElabRulesAux_spec__2___redArg();
                            return v___x_7221_;
                        } else {
                            v___x_7222_ = l_Lean_Syntax_getArg(v___x_7218_, v___x_7213_);
                            crate::leanh::lean_dec(v___x_7218_);
                            v_attrs_x3f_7223_ = l_Lean_Syntax_getArgs(v___x_7222_);
                            crate::leanh::lean_dec(v___x_7222_);
                            v___x_7224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_7224_, 0, v_attrs_x3f_7223_);
                            v___y_7184_ = v_doc_x3f_7210_;
                            v___y_7185_ = v___x_7213_;
                            v_attrs_x3f_7186_ = v___x_7224_;
                            v___y_7187_ = v___y_7211_;
                            v___y_7188_ = v___y_7212_;
                            state = 27;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_7214_);
                    v___x_7225_ = crate::leanh::lean_box(0);
                    v___y_7184_ = v_doc_x3f_7210_;
                    v___y_7185_ = v___x_7213_;
                    v_attrs_x3f_7186_ = v___x_7225_;
                    v___y_7187_ = v___y_7211_;
                    v___y_7188_ = v___y_7212_;
                    state = 27;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabElab___boxed(
    mut v_x_7237_: *mut crate::leanh::LeanObject,
    mut v_a_7238_: *mut crate::leanh::LeanObject,
    mut v_a_7239_: *mut crate::leanh::LeanObject,
    mut v_a_7240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7241_ = l_Lean_Elab_Command_elabElab(v_x_7237_, v_a_7238_, v_a_7239_);
    crate::leanh::lean_dec(v_a_7239_);
    crate::leanh::lean_dec_ref(v_a_7238_);
    return v_res_7241_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(
    mut v_00_u03b1_7242_: *mut crate::leanh::LeanObject,
    mut v_x_7243_: *mut crate::leanh::LeanObject,
    mut v___y_7244_: *mut crate::leanh::LeanObject,
    mut v___y_7245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7246_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___redArg(v_x_7243_, v___y_7245_);
    return v___x_7246_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1___boxed(
    mut v_00_u03b1_7247_: *mut crate::leanh::LeanObject,
    mut v_x_7248_: *mut crate::leanh::LeanObject,
    mut v___y_7249_: *mut crate::leanh::LeanObject,
    mut v___y_7250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7251_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__1(v_00_u03b1_7247_, v_x_7248_, v___y_7249_, v___y_7250_);
    crate::leanh::lean_dec_ref(v___y_7249_);
    crate::leanh::lean_dec_ref(v_x_7248_);
    return v_res_7251_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(
    mut v_00_u03b1_7252_: *mut crate::leanh::LeanObject,
    mut v_ref_7253_: *mut crate::leanh::LeanObject,
    mut v___y_7254_: *mut crate::leanh::LeanObject,
    mut v___y_7255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7257_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___redArg(v_ref_7253_);
    return v___x_7257_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5___boxed(
    mut v_00_u03b1_7258_: *mut crate::leanh::LeanObject,
    mut v_ref_7259_: *mut crate::leanh::LeanObject,
    mut v___y_7260_: *mut crate::leanh::LeanObject,
    mut v___y_7261_: *mut crate::leanh::LeanObject,
    mut v___y_7262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7263_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__5(v_00_u03b1_7258_, v_ref_7259_, v___y_7260_, v___y_7261_);
    crate::leanh::lean_dec(v___y_7261_);
    crate::leanh::lean_dec_ref(v___y_7260_);
    return v_res_7263_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(
    mut v_00_u03b1_7264_: *mut crate::leanh::LeanObject,
    mut v_x_7265_: *mut crate::leanh::LeanObject,
    mut v___y_7266_: *mut crate::leanh::LeanObject,
    mut v___y_7267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7269_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___redArg(
        v_x_7265_,
        v___y_7266_,
        v___y_7267_,
    );
    return v___x_7269_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0___boxed(
    mut v_00_u03b1_7270_: *mut crate::leanh::LeanObject,
    mut v_x_7271_: *mut crate::leanh::LeanObject,
    mut v___y_7272_: *mut crate::leanh::LeanObject,
    mut v___y_7273_: *mut crate::leanh::LeanObject,
    mut v___y_7274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7275_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0(
        v_00_u03b1_7270_,
        v_x_7271_,
        v___y_7272_,
        v___y_7273_,
    );
    crate::leanh::lean_dec(v___y_7273_);
    crate::leanh::lean_dec_ref(v___y_7272_);
    return v_res_7275_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(
    mut v_as_7276_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7277_: *mut crate::leanh::LeanObject,
    mut v_b_7278_: *mut crate::leanh::LeanObject,
    mut v_a_7279_: *mut crate::leanh::LeanObject,
    mut v___y_7280_: *mut crate::leanh::LeanObject,
    mut v___y_7281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7283_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___redArg(v_as_x27_7277_, v_b_7278_, v___y_7280_, v___y_7281_);
    return v___x_7283_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3___boxed(
    mut v_as_7284_: *mut crate::leanh::LeanObject,
    mut v_as_x27_7285_: *mut crate::leanh::LeanObject,
    mut v_b_7286_: *mut crate::leanh::LeanObject,
    mut v_a_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7291_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__3(v_as_7284_, v_as_x27_7285_, v_b_7286_, v_a_7287_, v___y_7288_, v___y_7289_);
    crate::leanh::lean_dec(v___y_7289_);
    crate::leanh::lean_dec_ref(v___y_7288_);
    crate::leanh::lean_dec(v_as_x27_7285_);
    crate::leanh::lean_dec(v_as_7284_);
    return v_res_7291_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(
    mut v_00_u03b2_7292_: *mut crate::leanh::LeanObject,
    mut v_m_7293_: *mut crate::leanh::LeanObject,
    mut v_a_7294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7295_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___redArg(v_m_7293_, v_a_7294_);
    return v___x_7295_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_7296_: *mut crate::leanh::LeanObject,
    mut v_m_7297_: *mut crate::leanh::LeanObject,
    mut v_a_7298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7299_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5(v_00_u03b2_7296_, v_m_7297_, v_a_7298_);
    crate::leanh::lean_dec(v_a_7298_);
    crate::leanh::lean_dec_ref(v_m_7297_);
    return v_res_7299_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(
    mut v_00_u03b2_7300_: *mut crate::leanh::LeanObject,
    mut v_x_7301_: *mut crate::leanh::LeanObject,
    mut v_x_7302_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7303_: u8 = 0;
    v___x_7303_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___redArg(v_x_7301_, v_x_7302_);
    return v___x_7303_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7___boxed(
    mut v_00_u03b2_7304_: *mut crate::leanh::LeanObject,
    mut v_x_7305_: *mut crate::leanh::LeanObject,
    mut v_x_7306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7307_: u8 = 0;
    let mut v_r_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7307_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7(v_00_u03b2_7304_, v_x_7305_, v_x_7306_);
    crate::leanh::lean_dec_ref(v_x_7306_);
    crate::leanh::lean_dec_ref(v_x_7305_);
    v_r_7308_ = crate::leanh::lean_box((v_res_7307_) as usize);
    return v_r_7308_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(
    mut v_00_u03b2_7309_: *mut crate::leanh::LeanObject,
    mut v_a_7310_: *mut crate::leanh::LeanObject,
    mut v_x_7311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7312_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___redArg(v_a_7310_, v_x_7311_);
    return v___x_7312_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10___boxed(
    mut v_00_u03b2_7313_: *mut crate::leanh::LeanObject,
    mut v_a_7314_: *mut crate::leanh::LeanObject,
    mut v_x_7315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7316_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__5_spec__10(v_00_u03b2_7313_, v_a_7314_, v_x_7315_);
    crate::leanh::lean_dec(v_x_7315_);
    crate::leanh::lean_dec(v_a_7314_);
    return v_res_7316_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(
    mut v_00_u03b2_7317_: *mut crate::leanh::LeanObject,
    mut v_x_7318_: *mut crate::leanh::LeanObject,
    mut v_x_7319_: usize,
    mut v_x_7320_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7321_: u8 = 0;
    v___x_7321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___redArg(v_x_7318_, v_x_7319_, v_x_7320_);
    return v___x_7321_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10___boxed(
    mut v_00_u03b2_7322_: *mut crate::leanh::LeanObject,
    mut v_x_7323_: *mut crate::leanh::LeanObject,
    mut v_x_7324_: *mut crate::leanh::LeanObject,
    mut v_x_7325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_21886__boxed_7326_: usize = 0;
    let mut v_res_7327_: u8 = 0;
    let mut v_r_7328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_21886__boxed_7326_ = crate::leanh::lean_unbox_usize(v_x_7324_);
    crate::leanh::lean_dec(v_x_7324_);
    v_res_7327_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10(v_00_u03b2_7322_, v_x_7323_, v_x_21886__boxed_7326_, v_x_7325_);
    crate::leanh::lean_dec_ref(v_x_7325_);
    crate::leanh::lean_dec_ref(v_x_7323_);
    v_r_7328_ = crate::leanh::lean_box((v_res_7327_) as usize);
    return v_r_7328_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(
    mut v_00_u03b2_7329_: *mut crate::leanh::LeanObject,
    mut v_keys_7330_: *mut crate::leanh::LeanObject,
    mut v_vals_7331_: *mut crate::leanh::LeanObject,
    mut v_heq_7332_: *mut crate::leanh::LeanObject,
    mut v_i_7333_: *mut crate::leanh::LeanObject,
    mut v_k_7334_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_7335_: u8 = 0;
    v___x_7335_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___redArg(v_keys_7330_, v_i_7333_, v_k_7334_);
    return v___x_7335_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13___boxed(
    mut v_00_u03b2_7336_: *mut crate::leanh::LeanObject,
    mut v_keys_7337_: *mut crate::leanh::LeanObject,
    mut v_vals_7338_: *mut crate::leanh::LeanObject,
    mut v_heq_7339_: *mut crate::leanh::LeanObject,
    mut v_i_7340_: *mut crate::leanh::LeanObject,
    mut v_k_7341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7342_: u8 = 0;
    let mut v_r_7343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7342_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Command_elabElab_spec__0_spec__2_spec__3_spec__7_spec__10_spec__13(v_00_u03b2_7336_, v_keys_7337_, v_vals_7338_, v_heq_7339_, v_i_7340_, v_k_7341_);
    crate::leanh::lean_dec_ref(v_k_7341_);
    crate::leanh::lean_dec_ref(v_vals_7338_);
    crate::leanh::lean_dec_ref(v_keys_7337_);
    v_r_7343_ = crate::leanh::lean_box((v_res_7342_) as usize);
    return v_r_7343_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7351_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_7352_ = l_Lean_Elab_Command_elabElab___closed__3;
    v___x_7353_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1;
    v___x_7354_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabElab___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_7355_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_7351_,
        v___x_7352_,
        v___x_7353_,
        v___x_7354_,
    );
    return v___x_7355_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___boxed(
    mut v_a_7356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7357_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
    return v_res_7357_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7384_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1___closed__1;
    v___x_7385_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___closed__6;
    v___x_7386_ = l_Lean_addBuiltinDeclarationRanges(v___x_7384_, v___x_7385_);
    return v___x_7386_;
}
pub unsafe fn l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3___boxed(
    mut v_a_7387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7388_ = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
    return v_res_7388_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_ElabRules(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lean_Elab_AuxDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElabRules___regBuiltin_Lean_Elab_Command_elabElabRules_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_ElabRules_0__Lean_Elab_Command_elabElab___regBuiltin_Lean_Elab_Command_elabElab_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_ElabRules(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_ElabRules(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Elab_AuxDef(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Do_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_ElabRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_ElabRules(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_ElabRules(builtin);
}
