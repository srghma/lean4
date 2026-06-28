// Lean compiler output
// Module: Lean.Elab.Quotation.Precheck
// Imports: Lean.Elab.Quotation.Util Lean.Elab.DeprecatedSyntax
use crate::r#gen::Init::Data::Array::Basic::l_Array_zip___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_isEmpty___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Macro_expandMacro_x3f___boxed, l_Lean_Name_append, l_Lean_Name_beq___boxed,
    l_Lean_Name_hash___override___boxed, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Name_mkStr6, l_Lean_Syntax_getArg,
    l_Lean_Syntax_getArgs, l_Lean_Syntax_getKind, l_Lean_Syntax_getPos_x3f,
    l_Lean_Syntax_getTailPos_x3f, l_Lean_Syntax_isOfKind, l_Lean_Syntax_matchesIdent,
    l_Lean_Syntax_matchesNull, l_Lean_maxRecDepthErrorMessage, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::MetaAttr::l_Lean_isMarkedMeta;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
};
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_empty, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
use crate::r#gen::Lean::DocString::Extension::l_Lean_addBuiltinDocString;
use crate::r#gen::Lean::Elab::DeprecatedSyntax::{
    initialize_Lean_Elab_DeprecatedSyntax, l_Lean_Elab_deprecatedSyntaxExt,
    l_Lean_Linter_linter_deprecated_syntax, runtime_initialize_Lean_Elab_DeprecatedSyntax,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::InfoTree::Main::l_Lean_Elab_realizeGlobalNameWithInfos;
use crate::r#gen::Lean::Elab::Quotation::Util::{
    initialize_Lean_Elab_Quotation_Util, l_Lean_Elab_Term_Quotation_hygiene,
    runtime_initialize_Lean_Elab_Quotation_Util,
};
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_adaptExpander, l_Lean_Elab_Term_resolveName,
    l_Lean_Elab_Term_termElabAttribute,
};
use crate::r#gen::Lean::Elab::Util::l_Lean_Elab_expandMacroImpl_x3f;
use crate::r#gen::Lean::EnvExtension::l_Lean_SimplePersistentEnvExtension_getState___redArg;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_instInhabitedEffectiveImport_default,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::ExtraModUses::{
    l___private_Lean_ExtraModUses_0__Lean_extraModUses, l_Lean_indirectModUseExt,
    l_Lean_instBEqExtraModUse_beq, l_Lean_instBEqExtraModUse_beq___boxed,
    l_Lean_instHashableExtraModUse_hash, l_Lean_instHashableExtraModUse_hash___boxed,
};
use crate::r#gen::Lean::InternalExceptionId::l_Lean_instBEqInternalExceptionId_beq;
use crate::r#gen::Lean::KeyedDeclsAttribute::{
    l_Lean_KeyedDeclsAttribute_addBuiltin___redArg, l_Lean_KeyedDeclsAttribute_evalIdentKey,
    l_Lean_KeyedDeclsAttribute_getValues___redArg, l_Lean_KeyedDeclsAttribute_init___redArg,
};
use crate::r#gen::Lean::Linter::Init::{
    l_Lean_Linter_getLinterValue, l_Lean_Linter_linterMessageTag, l_Lean_Linter_linterSetsExt,
};
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_joinSep,
    l_Lean_MessageData_note, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_MessageData_ofSyntax, l_Lean_MessageLog_add, l_Lean_indentD,
    l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Modifiers::l_Lean_mkPrivateName;
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ResolveName::{
    l_Lean_ResolveName_resolveGlobalName, l_Lean_ResolveName_resolveNamespace,
};
use crate::r#gen::Lean::Syntax::{l_Lean_Syntax_getQuotContent, l_Lean_Syntax_isAnyAntiquot};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
use crate::r#gen::Std::Data::HashMap::Basic::l_Std_HashMap_instInhabited;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
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
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt,
    lean_string_dec_eq, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [113, 117, 111, 116, 80, 114, 101, 99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10939830246731540712 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<236> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 236, m_capacity: 236, m_length: 235, m_data: [69, 110, 97, 98, 108, 101, 32, 101, 97, 103, 101, 114, 32, 110, 97, 109, 101, 32, 97, 110, 97, 108, 121, 115, 105, 115, 32, 111, 110, 32, 110, 111, 116, 97, 116, 105, 111, 110, 115, 32, 105, 110, 32, 111, 114, 100, 101, 114, 32, 116, 111, 32, 102, 105, 110, 100, 32, 117, 110, 98, 111, 117, 110, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 32, 101, 97, 114, 108, 121, 46, 10, 78, 111, 116, 101, 32, 116, 104, 97, 116, 32, 116, 121, 112, 101, 45, 115, 101, 110, 115, 105, 116, 105, 118, 101, 32, 115, 121, 110, 116, 97, 120, 32, 40, 34, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 115, 34, 41, 32, 110, 101, 101, 100, 115, 32, 115, 112, 101, 99, 105, 97, 108, 32, 115, 117, 112, 112, 111, 114, 116, 32, 102, 111, 114, 32, 116, 104, 105, 115, 32, 107, 105, 110, 100, 32, 111, 102, 32, 99, 104, 101, 99, 107, 44, 32, 115, 111, 32, 105, 116, 32, 109, 105, 103, 104, 116, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 116, 117, 114, 110, 101, 100, 32, 111, 102, 102, 32, 119, 104, 101, 110, 32, 117, 115, 105, 110, 103, 32, 115, 117, 99, 104, 32, 115, 121, 110, 116, 97, 120, 46, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [84, 101, 114, 109, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [81, 117, 111, 116, 97, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15108969580533659713 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [97, 108, 108, 111, 119, 83, 101, 99, 116, 105, 111, 110, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,10939830246731540712 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,14423494823855448 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value: crate::leanh::LeanStringObject<106> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 106, m_capacity: 106, m_length: 105, m_data: [65, 108, 108, 111, 119, 32, 111, 99, 99, 117, 114, 114, 101, 110, 99, 101, 115, 32, 111, 102, 32, 115, 101, 99, 116, 105, 111, 110, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 32, 105, 110, 32, 99, 104, 101, 99, 107, 101, 100, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 115, 44, 32, 105, 116, 32, 105, 115, 32, 117, 115, 101, 102, 117, 108, 32, 119, 104, 101, 110, 32, 100, 101, 99, 108, 97, 114, 105, 110, 103, 32, 108, 111, 99, 97, 108, 32, 110, 111, 116, 97, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_4: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,15108969580533659713 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value_aux_4) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,3171040061646861605 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [98, 117, 105, 108, 116, 105, 110, 95, 113, 117, 111, 116, 95, 112, 114, 101, 99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__2_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17836793041102043054 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [113, 117, 111, 116, 95, 112, 114, 101, 99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16164697219914666120 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 32, 97, 32, 100, 111, 117, 98, 108, 101, 32, 98, 97, 99, 107, 116, 105, 99, 107, 32, 115, 121, 110, 116, 97, 120, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 112, 114, 101, 45, 99, 104, 101, 99, 107, 46, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [80, 114, 101, 99, 104, 101, 99, 107, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7569105260126518697 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<6> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*6 + 0) as u16, other: 6, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 65, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__10_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4532218879029173189 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value: crate::leanh::LeanStringObject<522> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 522, m_capacity: 522, m_length: 521, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 100, 111, 117, 98, 108, 101, 32, 98, 97, 99, 107, 116, 105, 99, 107, 32, 115, 121, 110, 116, 97, 120, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 112, 114, 101, 45, 99, 104, 101, 99, 107, 46, 10, 10, 96, 64, 91, 113, 117, 111, 116, 95, 112, 114, 101, 99, 104, 101, 99, 107, 32, 107, 93, 96, 32, 114, 101, 103, 105, 115, 116, 101, 114, 115, 32, 97, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 111, 102, 32, 116, 121, 112, 101, 32, 96, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 101, 114, 109, 46, 81, 117, 111, 116, 97, 116, 105, 111, 110, 46, 80, 114, 101, 99, 104, 101, 99, 107, 96, 32, 102, 111, 114, 32, 116, 104, 101, 10, 115, 121, 110, 116, 97, 120, 32, 110, 111, 100, 101, 32, 107, 105, 110, 100, 32, 96, 107, 96, 46, 32, 73, 116, 32, 115, 104, 111, 117, 108, 100, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 32, 101, 97, 103, 101, 114, 32, 110, 97, 109, 101, 32, 97, 110, 97, 108, 121, 115, 105, 115, 32, 111, 110, 32, 116, 104, 101, 32, 112, 97, 115, 115, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 98, 121, 32, 116, 104, 114, 111, 119, 105, 110, 103, 32, 97, 110, 10, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 111, 110, 32, 117, 110, 98, 111, 117, 110, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 115, 44, 32, 97, 110, 100, 32, 99, 97, 108, 108, 105, 110, 103, 32, 96, 112, 114, 101, 99, 104, 101, 99, 107, 96, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 108, 121, 32, 111, 110, 32, 110, 101, 115, 116, 101, 100, 32, 116, 101, 114, 109, 115, 44, 32, 112, 111, 116, 101, 110, 116, 105, 97, 108, 108, 121, 10, 119, 105, 116, 104, 32, 97, 110, 32, 101, 120, 116, 101, 110, 100, 101, 100, 32, 108, 111, 99, 97, 108, 32, 99, 111, 110, 116, 101, 120, 116, 32, 40, 96, 119, 105, 116, 104, 78, 101, 119, 76, 111, 99, 97, 108, 96, 41, 46, 32, 77, 97, 99, 114, 111, 115, 32, 119, 105, 116, 104, 111, 117, 116, 32, 114, 101, 103, 105, 115, 116, 101, 114, 101, 100, 32, 112, 114, 101, 99, 104, 101, 99, 107, 32, 104, 111, 111, 107, 32, 97, 114, 101, 10, 117, 110, 102, 111, 108, 100, 101, 100, 44, 32, 97, 110, 100, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 45, 108, 101, 115, 115, 32, 115, 121, 110, 116, 97, 120, 32, 105, 115, 32, 117, 108, 116, 105, 109, 97, 116, 101, 108, 121, 32, 97, 115, 115, 117, 109, 101, 100, 32, 116, 111, 32, 98, 101, 32, 119, 101, 108, 108, 45, 102, 111, 114, 109, 101, 100, 46, 10, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 41 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 57 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 3 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 51 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 26 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 43 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [104, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value) as *mut crate::leanh::LeanObject,9871775667037945883 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0_value: crate::leanh::LeanStringObject<46> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [84, 104, 105, 115, 32, 108, 105, 110, 116, 101, 114, 32, 99, 97, 110, 32, 98, 101, 32, 100, 105, 115, 97, 98, 108, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [32, 102, 97, 108, 115, 101, 96, 0]};
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__1: usize = 0;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instBEqExtraModUse_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_instHashableExtraModUse_hash___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [101, 120, 116, 114, 97, 77, 111, 100, 85, 115, 101, 115, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__7_value) as *mut crate::leanh::LeanObject,7870113334857981723 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [32, 101, 120, 116, 114, 97, 32, 109, 111, 100, 32, 117, 115, 101, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [114, 101, 99, 111, 114, 100, 105, 110, 103, 32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 101, 103, 117, 108, 97, 114, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [109, 101, 116, 97, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [112, 117, 98, 108, 105, 99, 0]};
static mut l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22_value) as *mut crate::leanh::LeanObject;
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___closed__0: u64 = 0;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_beq___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Name_hash___override___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<158> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 158, m_capacity: 158, m_length: 157, m_data: [109, 97, 120, 105, 109, 117, 109, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 100, 101, 112, 116, 104, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 32, 60, 110, 117, 109, 62, 96, 32, 116, 111, 32, 105, 110, 99, 114, 101, 97, 115, 101, 32, 108, 105, 109, 105, 116, 10, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 115, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 103, 101, 116, 32, 100, 105, 97, 103, 110, 111, 115, 116, 105, 99, 32, 105, 110, 102, 111, 114, 109, 97, 116, 105, 111, 110, 0]};
static mut l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheck___closed__0_value: crate::leanh::LeanStringObject<
    57,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 57,
    m_capacity: 57,
    m_length: 56,
    m_data: [
        110, 111, 32, 109, 97, 99, 114, 111, 32, 111, 114, 32, 96, 91, 113, 117, 111, 116, 95, 112,
        114, 101, 99, 104, 101, 99, 107, 93, 96, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 102,
        111, 114, 32, 115, 121, 110, 116, 97, 120, 32, 107, 105, 110, 100, 32, 96, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheck___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheck___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheck___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheck___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheck___closed__2_value: crate::leanh::LeanStringObject<
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
    m_data: [96, 32, 102, 111, 117, 110, 100, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheck___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheck___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheck___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheck___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheck___closed__4_value: crate::leanh::LeanStringObject<
    152,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 152,
    m_capacity: 152,
    m_length: 151,
    m_data: [
        10, 84, 104, 105, 115, 32, 109, 101, 97, 110, 115, 32, 119, 101, 32, 99, 97, 110, 110, 111,
        116, 32, 101, 97, 103, 101, 114, 108, 121, 32, 99, 104, 101, 99, 107, 32, 121, 111, 117,
        114, 32, 110, 111, 116, 97, 116, 105, 111, 110, 47, 113, 117, 111, 116, 97, 116, 105, 111,
        110, 32, 102, 111, 114, 32, 117, 110, 98, 111, 117, 110, 100, 32, 105, 100, 101, 110, 116,
        105, 102, 105, 101, 114, 115, 59, 32, 121, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101,
        32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 113, 117, 111, 116, 80, 114,
        101, 99, 104, 101, 99, 107, 32, 102, 97, 108, 115, 101, 96, 32, 116, 111, 32, 100, 105,
        115, 97, 98, 108, 101, 32, 116, 104, 105, 115, 32, 99, 104, 101, 99, 107, 46, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheck___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheck___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheck___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheck___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheck___closed__6_value: crate::leanh::LeanStringObject<
    35,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 117, 115, 101, 115, 32, 100, 101, 112, 114,
        101, 99, 97, 116, 101, 100, 32, 115, 121, 110, 116, 97, 120, 32, 39, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheck___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheck___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheck___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheck___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheck___closed__8_value: crate::leanh::LeanStringObject<
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
    m_data: [39, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheck___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheck___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheck___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheck___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheck___closed__10_value: crate::leanh::LeanStringObject<
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
    m_data: [58, 32, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheck___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheck___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheck___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheck___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckIdent___closed__0_value:
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
        85, 110, 107, 110, 111, 119, 110, 32, 105, 100, 101, 110, 116, 105, 102, 105, 101, 114, 32,
        96, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheckIdent___closed__2_value:
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
        96, 32, 97, 116, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 112, 114, 101, 99,
        104, 101, 99, 107, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheckIdent___closed__4_value:
    crate::leanh::LeanStringObject<67> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 67,
    m_capacity: 67,
    m_length: 66,
    m_data: [
        89, 111, 117, 32, 99, 97, 110, 32, 117, 115, 101, 32, 96, 115, 101, 116, 95, 111, 112, 116,
        105, 111, 110, 32, 113, 117, 111, 116, 80, 114, 101, 99, 104, 101, 99, 107, 32, 102, 97,
        108, 115, 101, 96, 32, 116, 111, 32, 100, 105, 115, 97, 98, 108, 101, 32, 116, 104, 105,
        115, 32, 99, 104, 101, 99, 107, 46, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckIdent___closed__5_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__4_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheckIdent___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [105, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__0_value) as *mut crate::leanh::LeanObject,5117844058249666356 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 73, 100, 101, 110, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__2_value) as *mut crate::leanh::LeanObject,131833293735037314 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [110, 97, 109, 101, 100, 65, 114, 103, 117, 109, 101, 110, 116, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,13594530736035158498 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [101, 108, 108, 105, 112, 115, 105, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__3_value) as *mut crate::leanh::LeanObject,15691513163239863397 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value:
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
static mut l_Lean_Elab_Term_Quotation_precheckApp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckApp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12966880221525079621 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckApp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckApp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 65, 112, 112, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__0_value) as *mut crate::leanh::LeanObject,10623999185646905507 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value:
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
        116, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value:
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
            l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5346268661279150583 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value:
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
        104, 121, 103, 105, 101, 110, 105, 99, 76, 80, 97, 114, 101, 110, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value:
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
            l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__2_value)
            as *mut crate::leanh::LeanObject,
        7306243862518720553 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 84, 121, 112, 101, 65, 115, 99, 114, 105, 112, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__0_value) as *mut crate::leanh::LeanObject,6785817859343234783 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value:
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
    m_data: [101, 120, 112, 108, 105, 99, 105, 116, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13290931718435096973 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 69, 120, 112, 108, 105, 99, 105, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__0_value) as *mut crate::leanh::LeanObject,10917974608318672570 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheckChoice___closed__0_value:
    crate::leanh::LeanStringObject<110> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 110,
    m_capacity: 110,
    m_length: 109,
    m_data: [
        97, 109, 98, 105, 103, 117, 111, 117, 115, 32, 110, 111, 116, 97, 116, 105, 111, 110, 32,
        119, 105, 116, 104, 32, 97, 116, 32, 108, 101, 97, 115, 116, 32, 111, 110, 101, 32, 105,
        110, 116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 32, 116, 104, 97, 116, 32,
        102, 97, 105, 108, 101, 100, 32, 113, 117, 111, 116, 97, 116, 105, 111, 110, 32, 112, 114,
        101, 99, 104, 101, 99, 107, 44, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 105, 110,
        116, 101, 114, 112, 114, 101, 116, 97, 116, 105, 111, 110, 115, 32, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckChoice___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckChoice___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheckChoice___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheckChoice___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Term_Quotation_precheckChoice___closed__2_value:
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
    m_data: [10, 10, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckChoice___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckChoice___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Term_Quotation_precheckChoice___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Term_Quotation_precheckChoice___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [99, 104, 111, 105, 99, 101, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__0_value) as *mut crate::leanh::LeanObject,11985596712582660667 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 67, 104, 111, 105, 99, 101, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__2_value) as *mut crate::leanh::LeanObject,13298686239476250843 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 101, 100, 81, 117, 111, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__0_value) as *mut crate::leanh::LeanObject,6990640787528865390 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 80, 114, 101, 99, 104, 101, 99, 107, 101, 100, 81, 117, 111, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__2_value) as *mut crate::leanh::LeanObject,14267400576367458620 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 139 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 142 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__0_value) as *mut crate::leanh::LeanObject,((( 36 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__1_value) as *mut crate::leanh::LeanObject,((( 60 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 139 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 40 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 139 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__3_value) as *mut crate::leanh::LeanObject,((( 40 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__4_value) as *mut crate::leanh::LeanObject,((( 58 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__2_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__5_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value:
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
    m_data: [98, 105, 110, 114, 101, 108, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11955267307951615569 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 66, 105, 110, 114, 101, 108, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__0_value) as *mut crate::leanh::LeanObject,12890662578808874579 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value:
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
        98, 105, 110, 114, 101, 108, 95, 110, 111, 95, 112, 114, 111, 112, 0,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2715876919967644250 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 66, 105, 110, 114, 101, 108, 78, 111, 80, 114, 111, 112, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__0_value) as *mut crate::leanh::LeanObject,3675832699139787489 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value:
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
    m_data: [98, 105, 110, 111, 112, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinop___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinop___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13783595361449278767 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinop___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinop___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 66, 105, 110, 111, 112, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__0_value) as *mut crate::leanh::LeanObject,1972647186140041680 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value:
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
    m_data: [98, 105, 110, 111, 112, 95, 108, 97, 122, 121, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11817042004572560931 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 66, 105, 110, 111, 112, 76, 97, 122, 121, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__0_value) as *mut crate::leanh::LeanObject,8976493910343761884 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value:
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
    m_data: [108, 101, 102, 116, 97, 99, 116, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7741897161554968299 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 76, 101, 102, 116, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__0_value) as *mut crate::leanh::LeanObject,16474700505668652794 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value:
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
    m_data: [114, 105, 103, 104, 116, 97, 99, 116, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckRightact___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckRightact___closed__0_value)
            as *mut crate::leanh::LeanObject,
        5088148737201669779 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckRightact___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckRightact___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 82, 105, 103, 104, 116, 97, 99, 116, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__0_value) as *mut crate::leanh::LeanObject,7900364419472768878 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value:
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
    m_data: [117, 110, 111, 112, 0],
};
static mut l_Lean_Elab_Term_Quotation_precheckUnop___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckUnop___closed__0_value)
            as *mut crate::leanh::LeanObject,
        9631422487873846596 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Term_Quotation_precheckUnop___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Term_Quotation_precheckUnop___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 85, 110, 111, 112, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__0_value) as *mut crate::leanh::LeanObject,5780821792438437060 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,8018486133748762727 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,16572064140653406795 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__0_value) as *mut crate::leanh::LeanObject,14482368511717255947 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [112, 114, 101, 99, 104, 101, 99, 107, 72, 121, 103, 105, 101, 110, 101, 73, 110, 102, 111, 0]};
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__6_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7892421401833366012 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__7_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__value) as *mut crate::leanh::LeanObject,7312483928035130638 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__1_value) as *mut crate::leanh::LeanObject,13368168967494448033 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocal___redArg(
    mut v_l_3216_: *mut crate::leanh::LeanObject,
    mut v_x_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_a_3224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_3218_);
    v___x_3226_ = l_Lean_NameSet_insert(v_a_3218_, v_l_3216_);
    crate::leanh::lean_inc(v_a_3224_);
    crate::leanh::lean_inc_ref(v_a_3223_);
    crate::leanh::lean_inc(v_a_3222_);
    crate::leanh::lean_inc_ref(v_a_3221_);
    crate::leanh::lean_inc(v_a_3220_);
    crate::leanh::lean_inc_ref(v_a_3219_);
    v___x_3227_ = crate::leanh::lean_apply_8(
        v_x_3217_,
        v___x_3226_,
        v_a_3219_,
        v_a_3220_,
        v_a_3221_,
        v_a_3222_,
        v_a_3223_,
        v_a_3224_,
        crate::leanh::lean_box(0),
    );
    return v___x_3227_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocal___redArg___boxed(
    mut v_l_3228_: *mut crate::leanh::LeanObject,
    mut v_x_3229_: *mut crate::leanh::LeanObject,
    mut v_a_3230_: *mut crate::leanh::LeanObject,
    mut v_a_3231_: *mut crate::leanh::LeanObject,
    mut v_a_3232_: *mut crate::leanh::LeanObject,
    mut v_a_3233_: *mut crate::leanh::LeanObject,
    mut v_a_3234_: *mut crate::leanh::LeanObject,
    mut v_a_3235_: *mut crate::leanh::LeanObject,
    mut v_a_3236_: *mut crate::leanh::LeanObject,
    mut v_a_3237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3238_ = l_Lean_Elab_Term_Quotation_withNewLocal___redArg(
        v_l_3228_, v_x_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_,
        v_a_3236_,
    );
    crate::leanh::lean_dec(v_a_3236_);
    crate::leanh::lean_dec_ref(v_a_3235_);
    crate::leanh::lean_dec(v_a_3234_);
    crate::leanh::lean_dec_ref(v_a_3233_);
    crate::leanh::lean_dec(v_a_3232_);
    crate::leanh::lean_dec_ref(v_a_3231_);
    crate::leanh::lean_dec(v_a_3230_);
    return v_res_3238_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocal(
    mut v_00_u03b1_3239_: *mut crate::leanh::LeanObject,
    mut v_l_3240_: *mut crate::leanh::LeanObject,
    mut v_x_3241_: *mut crate::leanh::LeanObject,
    mut v_a_3242_: *mut crate::leanh::LeanObject,
    mut v_a_3243_: *mut crate::leanh::LeanObject,
    mut v_a_3244_: *mut crate::leanh::LeanObject,
    mut v_a_3245_: *mut crate::leanh::LeanObject,
    mut v_a_3246_: *mut crate::leanh::LeanObject,
    mut v_a_3247_: *mut crate::leanh::LeanObject,
    mut v_a_3248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3250_ = l_Lean_Elab_Term_Quotation_withNewLocal___redArg(
        v_l_3240_, v_x_3241_, v_a_3242_, v_a_3243_, v_a_3244_, v_a_3245_, v_a_3246_, v_a_3247_,
        v_a_3248_,
    );
    return v___x_3250_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocal___boxed(
    mut v_00_u03b1_3251_: *mut crate::leanh::LeanObject,
    mut v_l_3252_: *mut crate::leanh::LeanObject,
    mut v_x_3253_: *mut crate::leanh::LeanObject,
    mut v_a_3254_: *mut crate::leanh::LeanObject,
    mut v_a_3255_: *mut crate::leanh::LeanObject,
    mut v_a_3256_: *mut crate::leanh::LeanObject,
    mut v_a_3257_: *mut crate::leanh::LeanObject,
    mut v_a_3258_: *mut crate::leanh::LeanObject,
    mut v_a_3259_: *mut crate::leanh::LeanObject,
    mut v_a_3260_: *mut crate::leanh::LeanObject,
    mut v_a_3261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3262_ = l_Lean_Elab_Term_Quotation_withNewLocal(
        v_00_u03b1_3251_,
        v_l_3252_,
        v_x_3253_,
        v_a_3254_,
        v_a_3255_,
        v_a_3256_,
        v_a_3257_,
        v_a_3258_,
        v_a_3259_,
        v_a_3260_,
    );
    crate::leanh::lean_dec(v_a_3260_);
    crate::leanh::lean_dec_ref(v_a_3259_);
    crate::leanh::lean_dec(v_a_3258_);
    crate::leanh::lean_dec_ref(v_a_3257_);
    crate::leanh::lean_dec(v_a_3256_);
    crate::leanh::lean_dec_ref(v_a_3255_);
    crate::leanh::lean_dec(v_a_3254_);
    return v_res_3262_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(
    mut v_as_3263_: *mut crate::leanh::LeanObject,
    mut v_i_3264_: usize,
    mut v_stop_3265_: usize,
    mut v_b_3266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3267_: u8 = 0;
    let mut v___x_3268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: usize = 0;
    let mut v___x_3271_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3267_ = lean_usize_dec_eq(v_i_3264_, v_stop_3265_);
                if v___x_3267_ == 0 {
                    v___x_3268_ = lean_array_uget_borrowed(v_as_3263_, v_i_3264_);
                    crate::leanh::lean_inc(v___x_3268_);
                    v___x_3269_ = l_Lean_NameSet_insert(v_b_3266_, v___x_3268_);
                    v___x_3270_ = 1usize;
                    v___x_3271_ = lean_usize_add(v_i_3264_, v___x_3270_);
                    v_i_3264_ = v___x_3271_;
                    v_b_3266_ = v___x_3269_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3266_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0___boxed(
    mut v_as_3273_: *mut crate::leanh::LeanObject,
    mut v_i_3274_: *mut crate::leanh::LeanObject,
    mut v_stop_3275_: *mut crate::leanh::LeanObject,
    mut v_b_3276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3277_: usize = 0;
    let mut v_stop_boxed_3278_: usize = 0;
    let mut v_res_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3277_ = crate::leanh::lean_unbox_usize(v_i_3274_);
    crate::leanh::lean_dec(v_i_3274_);
    v_stop_boxed_3278_ = crate::leanh::lean_unbox_usize(v_stop_3275_);
    crate::leanh::lean_dec(v_stop_3275_);
    v_res_3279_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_as_3273_, v_i_boxed_3277_, v_stop_boxed_3278_, v_b_3276_);
    crate::leanh::lean_dec_ref(v_as_3273_);
    return v_res_3279_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocals___redArg(
    mut v_ls_3280_: *mut crate::leanh::LeanObject,
    mut v_x_3281_: *mut crate::leanh::LeanObject,
    mut v_a_3282_: *mut crate::leanh::LeanObject,
    mut v_a_3283_: *mut crate::leanh::LeanObject,
    mut v_a_3284_: *mut crate::leanh::LeanObject,
    mut v_a_3285_: *mut crate::leanh::LeanObject,
    mut v_a_3286_: *mut crate::leanh::LeanObject,
    mut v_a_3287_: *mut crate::leanh::LeanObject,
    mut v_a_3288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: u8 = 0;
    v___x_3290_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3291_ = lean_array_get_size(v_ls_3280_);
    v___x_3292_ = lean_nat_dec_lt(v___x_3290_, v___x_3291_);
    if v___x_3292_ == 0 {
        let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_a_3288_);
        crate::leanh::lean_inc_ref(v_a_3287_);
        crate::leanh::lean_inc(v_a_3286_);
        crate::leanh::lean_inc_ref(v_a_3285_);
        crate::leanh::lean_inc(v_a_3284_);
        crate::leanh::lean_inc_ref(v_a_3283_);
        crate::leanh::lean_inc(v_a_3282_);
        v___x_3293_ = crate::leanh::lean_apply_8(
            v_x_3281_,
            v_a_3282_,
            v_a_3283_,
            v_a_3284_,
            v_a_3285_,
            v_a_3286_,
            v_a_3287_,
            v_a_3288_,
            crate::leanh::lean_box(0),
        );
        return v___x_3293_;
    } else {
        let mut v___x_3294_: u8 = 0;
        v___x_3294_ = lean_nat_dec_le(v___x_3291_, v___x_3291_);
        if v___x_3294_ == 0 {
            if v___x_3292_ == 0 {
                let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_a_3288_);
                crate::leanh::lean_inc_ref(v_a_3287_);
                crate::leanh::lean_inc(v_a_3286_);
                crate::leanh::lean_inc_ref(v_a_3285_);
                crate::leanh::lean_inc(v_a_3284_);
                crate::leanh::lean_inc_ref(v_a_3283_);
                crate::leanh::lean_inc(v_a_3282_);
                v___x_3295_ = crate::leanh::lean_apply_8(
                    v_x_3281_,
                    v_a_3282_,
                    v_a_3283_,
                    v_a_3284_,
                    v_a_3285_,
                    v_a_3286_,
                    v_a_3287_,
                    v_a_3288_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3295_;
            } else {
                let mut v___x_3296_: usize = 0;
                let mut v___x_3297_: usize = 0;
                let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3296_ = 0usize;
                v___x_3297_ = lean_usize_of_nat(v___x_3291_);
                crate::leanh::lean_inc(v_a_3282_);
                v___x_3298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_ls_3280_, v___x_3296_, v___x_3297_, v_a_3282_);
                crate::leanh::lean_inc(v_a_3288_);
                crate::leanh::lean_inc_ref(v_a_3287_);
                crate::leanh::lean_inc(v_a_3286_);
                crate::leanh::lean_inc_ref(v_a_3285_);
                crate::leanh::lean_inc(v_a_3284_);
                crate::leanh::lean_inc_ref(v_a_3283_);
                v___x_3299_ = crate::leanh::lean_apply_8(
                    v_x_3281_,
                    v___x_3298_,
                    v_a_3283_,
                    v_a_3284_,
                    v_a_3285_,
                    v_a_3286_,
                    v_a_3287_,
                    v_a_3288_,
                    crate::leanh::lean_box(0),
                );
                return v___x_3299_;
            }
        } else {
            let mut v___x_3300_: usize = 0;
            let mut v___x_3301_: usize = 0;
            let mut v___x_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_3300_ = 0usize;
            v___x_3301_ = lean_usize_of_nat(v___x_3291_);
            crate::leanh::lean_inc(v_a_3282_);
            v___x_3302_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Term_Quotation_withNewLocals_spec__0(v_ls_3280_, v___x_3300_, v___x_3301_, v_a_3282_);
            crate::leanh::lean_inc(v_a_3288_);
            crate::leanh::lean_inc_ref(v_a_3287_);
            crate::leanh::lean_inc(v_a_3286_);
            crate::leanh::lean_inc_ref(v_a_3285_);
            crate::leanh::lean_inc(v_a_3284_);
            crate::leanh::lean_inc_ref(v_a_3283_);
            v___x_3303_ = crate::leanh::lean_apply_8(
                v_x_3281_,
                v___x_3302_,
                v_a_3283_,
                v_a_3284_,
                v_a_3285_,
                v_a_3286_,
                v_a_3287_,
                v_a_3288_,
                crate::leanh::lean_box(0),
            );
            return v___x_3303_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocals___redArg___boxed(
    mut v_ls_3304_: *mut crate::leanh::LeanObject,
    mut v_x_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3314_ = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(
        v_ls_3304_, v_x_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_,
        v_a_3312_,
    );
    crate::leanh::lean_dec(v_a_3312_);
    crate::leanh::lean_dec_ref(v_a_3311_);
    crate::leanh::lean_dec(v_a_3310_);
    crate::leanh::lean_dec_ref(v_a_3309_);
    crate::leanh::lean_dec(v_a_3308_);
    crate::leanh::lean_dec_ref(v_a_3307_);
    crate::leanh::lean_dec(v_a_3306_);
    crate::leanh::lean_dec_ref(v_ls_3304_);
    return v_res_3314_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocals(
    mut v_00_u03b1_3315_: *mut crate::leanh::LeanObject,
    mut v_ls_3316_: *mut crate::leanh::LeanObject,
    mut v_x_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
    mut v_a_3320_: *mut crate::leanh::LeanObject,
    mut v_a_3321_: *mut crate::leanh::LeanObject,
    mut v_a_3322_: *mut crate::leanh::LeanObject,
    mut v_a_3323_: *mut crate::leanh::LeanObject,
    mut v_a_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3326_ = l_Lean_Elab_Term_Quotation_withNewLocals___redArg(
        v_ls_3316_, v_x_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_, v_a_3322_, v_a_3323_,
        v_a_3324_,
    );
    return v___x_3326_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_withNewLocals___boxed(
    mut v_00_u03b1_3327_: *mut crate::leanh::LeanObject,
    mut v_ls_3328_: *mut crate::leanh::LeanObject,
    mut v_x_3329_: *mut crate::leanh::LeanObject,
    mut v_a_3330_: *mut crate::leanh::LeanObject,
    mut v_a_3331_: *mut crate::leanh::LeanObject,
    mut v_a_3332_: *mut crate::leanh::LeanObject,
    mut v_a_3333_: *mut crate::leanh::LeanObject,
    mut v_a_3334_: *mut crate::leanh::LeanObject,
    mut v_a_3335_: *mut crate::leanh::LeanObject,
    mut v_a_3336_: *mut crate::leanh::LeanObject,
    mut v_a_3337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3338_ = l_Lean_Elab_Term_Quotation_withNewLocals(
        v_00_u03b1_3327_,
        v_ls_3328_,
        v_x_3329_,
        v_a_3330_,
        v_a_3331_,
        v_a_3332_,
        v_a_3333_,
        v_a_3334_,
        v_a_3335_,
        v_a_3336_,
    );
    crate::leanh::lean_dec(v_a_3336_);
    crate::leanh::lean_dec_ref(v_a_3335_);
    crate::leanh::lean_dec(v_a_3334_);
    crate::leanh::lean_dec_ref(v_a_3333_);
    crate::leanh::lean_dec(v_a_3332_);
    crate::leanh::lean_dec_ref(v_a_3331_);
    crate::leanh::lean_dec(v_a_3330_);
    crate::leanh::lean_dec_ref(v_ls_3328_);
    return v_res_3338_;
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(
    mut v_name_3339_: *mut crate::leanh::LeanObject,
    mut v_decl_3340_: *mut crate::leanh::LeanObject,
    mut v_ref_3341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_defValue_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_descr_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3347_: u8 = 0;
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3352_: u8 = 0;
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut v_unused_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3366_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3343_ = crate::leanh::lean_ctor_get(v_decl_3340_, 0);
                v_descr_3344_ = crate::leanh::lean_ctor_get(v_decl_3340_, 1);
                v_deprecation_x3f_3345_ = crate::leanh::lean_ctor_get(v_decl_3340_, 2);
                v___x_3346_ = crate::leanh::lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3347_ = (crate::leanh::lean_unbox(v_defValue_3343_) as u8);
                crate::leanh::lean_ctor_set_uint8(v___x_3346_, 0 as u32, v___x_3347_);
                crate::leanh::lean_inc(v_deprecation_x3f_3345_);
                crate::leanh::lean_inc_ref(v_descr_3344_);
                crate::leanh::lean_inc_n(v_name_3339_, 2);
                v___x_3348_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3348_, 0, v_name_3339_);
                crate::leanh::lean_ctor_set(v___x_3348_, 1, v_ref_3341_);
                crate::leanh::lean_ctor_set(v___x_3348_, 2, v___x_3346_);
                crate::leanh::lean_ctor_set(v___x_3348_, 3, v_descr_3344_);
                crate::leanh::lean_ctor_set(v___x_3348_, 4, v_deprecation_x3f_3345_);
                v___x_3349_ = lean_register_option(v_name_3339_, v___x_3348_);
                if crate::leanh::lean_obj_tag(v___x_3349_) == 0 {
                    v_isSharedCheck_3357_ = (!crate::leanh::lean_is_exclusive(v___x_3349_)) as u8;
                    if v_isSharedCheck_3357_ == 0 {
                        v_unused_3358_ = crate::leanh::lean_ctor_get(v___x_3349_, 0);
                        crate::leanh::lean_dec(v_unused_3358_);
                        v___x_3351_ = v___x_3349_;
                        v_isShared_3352_ = v_isSharedCheck_3357_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3349_);
                        v___x_3351_ = crate::leanh::lean_box(0);
                        v_isShared_3352_ = v_isSharedCheck_3357_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_name_3339_);
                    v_a_3359_ = crate::leanh::lean_ctor_get(v___x_3349_, 0);
                    v_isSharedCheck_3366_ = (!crate::leanh::lean_is_exclusive(v___x_3349_)) as u8;
                    if v_isSharedCheck_3366_ == 0 {
                        v___x_3361_ = v___x_3349_;
                        v_isShared_3362_ = v_isSharedCheck_3366_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3359_);
                        crate::leanh::lean_dec(v___x_3349_);
                        v___x_3361_ = crate::leanh::lean_box(0);
                        v_isShared_3362_ = v_isSharedCheck_3366_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_defValue_3343_);
                v___x_3353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3353_, 0, v_name_3339_);
                crate::leanh::lean_ctor_set(v___x_3353_, 1, v_defValue_3343_);
                if v_isShared_3352_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3351_, 0, v___x_3353_);
                    v___x_3355_ = v___x_3351_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
                    v___x_3355_ = v_reuseFailAlloc_3356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3355_;
            }
            3 => {
                if v_isShared_3362_ == 0 {
                    v___x_3364_ = v___x_3361_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3365_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
                    v___x_3364_ = v_reuseFailAlloc_3365_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3367_: *mut crate::leanh::LeanObject,
    mut v_decl_3368_: *mut crate::leanh::LeanObject,
    mut v_ref_3369_: *mut crate::leanh::LeanObject,
    mut v_a_3370_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3371_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v_name_3367_, v_decl_3368_, v_ref_3369_);
    crate::leanh::lean_dec_ref(v_decl_3368_);
    return v_res_3371_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3392_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_;
    v___x_3393_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_;
    v___x_3394_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__8_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_;
    v___x_3395_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_3392_, v___x_3393_, v___x_3394_);
    return v___x_3395_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4____boxed(
    mut v_a_3396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3397_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
    return v_res_3397_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__1_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_;
    v___x_3417_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__3_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_;
    v___x_3418_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__4_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_;
    v___x_3419_ = l_Lean_Option_register___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4__spec__0(v___x_3416_, v___x_3417_, v___x_3418_);
    return v___x_3419_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4____boxed(
    mut v_a_3420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3421_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
    return v_res_3421_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(
    mut v_builtin_3422_: u8,
    mut v_stx_3423_: *mut crate::leanh::LeanObject,
    mut v___y_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3427_ = l_Lean_KeyedDeclsAttribute_evalIdentKey(v_stx_3423_, v___y_3424_, v___y_3425_);
    return v___x_3427_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(
    mut v_builtin_3428_: *mut crate::leanh::LeanObject,
    mut v_stx_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
    mut v___y_3432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_builtin_boxed_3433_: u8 = 0;
    let mut v_res_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3433_ = (crate::leanh::lean_unbox(v_builtin_3428_) as u8);
    v_res_3434_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__0_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_3433_, v_stx_3429_, v___y_3430_, v___y_3431_);
    crate::leanh::lean_dec(v___y_3431_);
    crate::leanh::lean_dec_ref(v___y_3430_);
    return v_res_3434_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(
    mut v_builtin_3435_: u8,
    mut v_declName_3436_: *mut crate::leanh::LeanObject,
    mut v_key_3437_: *mut crate::leanh::LeanObject,
    mut v___y_3438_: *mut crate::leanh::LeanObject,
    mut v___y_3439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3441_ = crate::leanh::lean_box(0);
    v___x_3442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3442_, 0, v___x_3441_);
    return v___x_3442_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(
    mut v_builtin_3443_: *mut crate::leanh::LeanObject,
    mut v_declName_3444_: *mut crate::leanh::LeanObject,
    mut v_key_3445_: *mut crate::leanh::LeanObject,
    mut v___y_3446_: *mut crate::leanh::LeanObject,
    mut v___y_3447_: *mut crate::leanh::LeanObject,
    mut v___y_3448_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_builtin_boxed_3449_: u8 = 0;
    let mut v_res_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_builtin_boxed_3449_ = (crate::leanh::lean_unbox(v_builtin_3443_) as u8);
    v_res_3450_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___lam__1_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_(v_builtin_boxed_3449_, v_declName_3444_, v_key_3445_, v___y_3446_, v___y_3447_);
    crate::leanh::lean_dec(v___y_3447_);
    crate::leanh::lean_dec_ref(v___y_3446_);
    crate::leanh::lean_dec(v_key_3445_);
    crate::leanh::lean_dec(v_declName_3444_);
    return v_res_3450_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3482_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__9_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_;
    v___x_3483_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_;
    v___x_3484_ = l_Lean_KeyedDeclsAttribute_init___redArg(v___x_3482_, v___x_3483_);
    return v___x_3484_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2____boxed(
    mut v_a_3485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3486_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
    return v_res_3486_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3489_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_;
    v___x_3490_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___closed__0;
    v___x_3491_ = l_Lean_addBuiltinDocString(v___x_3489_, v___x_3490_);
    return v___x_3491_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1___boxed(
    mut v_a_3492_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3493_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
    return v_res_3493_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3520_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__11_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_;
    v___x_3521_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___closed__6;
    v___x_3522_ = l_Lean_addBuiltinDeclarationRanges(v___x_3520_, v___x_3521_);
    return v___x_3522_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3___boxed(
    mut v_a_3523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3524_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
    return v_res_3524_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(
    mut v_x_3528_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3528_) == 3 {
        let mut v___x_3529_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_x_3528_, 4);
        v___x_3529_ = 1;
        return v___x_3529_;
    } else {
        let mut v___x_3530_: u8 = 0;
        crate::leanh::lean_inc(v_x_3528_);
        v___x_3530_ = l_Lean_Syntax_isAnyAntiquot(v_x_3528_);
        if v___x_3530_ == 0 {
            let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3532_: u8 = 0;
            v___x_3531_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1;
            crate::leanh::lean_inc(v_x_3528_);
            v___x_3532_ = l_Lean_Syntax_isOfKind(v_x_3528_, v___x_3531_);
            if v___x_3532_ == 0 {
                let mut v___x_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3536_: u8 = 0;
                v___x_3533_ = l_Lean_Syntax_getArgs(v_x_3528_);
                crate::leanh::lean_dec(v_x_3528_);
                v___x_3534_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3535_ = lean_array_get_size(v___x_3533_);
                v___x_3536_ = lean_nat_dec_lt(v___x_3534_, v___x_3535_);
                if v___x_3536_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3533_);
                    return v___x_3532_;
                } else {
                    if v___x_3536_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3533_);
                        return v___x_3532_;
                    } else {
                        let mut v___x_3537_: usize = 0;
                        let mut v___x_3538_: usize = 0;
                        let mut v___x_3539_: u8 = 0;
                        v___x_3537_ = 0usize;
                        v___x_3538_ = lean_usize_of_nat(v___x_3535_);
                        v___x_3539_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v___x_3533_, v___x_3537_, v___x_3538_);
                        crate::leanh::lean_dec_ref(v___x_3533_);
                        return v___x_3539_;
                    }
                }
            } else {
                crate::leanh::lean_dec(v_x_3528_);
                return v___x_3530_;
            }
        } else {
            let mut v___x_3540_: u8 = 0;
            crate::leanh::lean_dec(v_x_3528_);
            v___x_3540_ = 0;
            return v___x_3540_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(
    mut v_as_3541_: *mut crate::leanh::LeanObject,
    mut v_i_3542_: usize,
    mut v_stop_3543_: usize,
) -> u8 {
    let mut v___x_3544_: u8 = 0;
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3546_: u8 = 0;
    let mut v___x_3547_: usize = 0;
    let mut v___x_3548_: usize = 0;
    let mut v___x_3550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3544_ = lean_usize_dec_eq(v_i_3542_, v_stop_3543_);
                if v___x_3544_ == 0 {
                    v___x_3545_ = lean_array_uget_borrowed(v_as_3541_, v_i_3542_);
                    crate::leanh::lean_inc(v___x_3545_);
                    v___x_3546_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v___x_3545_);
                    if v___x_3546_ == 0 {
                        v___x_3547_ = 1usize;
                        v___x_3548_ = lean_usize_add(v_i_3542_, v___x_3547_);
                        v_i_3542_ = v___x_3548_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3546_;
                    }
                } else {
                    v___x_3550_ = 0;
                    return v___x_3550_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0___boxed(
    mut v_as_3551_: *mut crate::leanh::LeanObject,
    mut v_i_3552_: *mut crate::leanh::LeanObject,
    mut v_stop_3553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3554_: usize = 0;
    let mut v_stop_boxed_3555_: usize = 0;
    let mut v_res_3556_: u8 = 0;
    let mut v_r_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3554_ = crate::leanh::lean_unbox_usize(v_i_3552_);
    crate::leanh::lean_dec(v_i_3552_);
    v_stop_boxed_3555_ = crate::leanh::lean_unbox_usize(v_stop_3553_);
    crate::leanh::lean_dec(v_stop_3553_);
    v_res_3556_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent_spec__0(v_as_3551_, v_i_boxed_3554_, v_stop_boxed_3555_);
    crate::leanh::lean_dec_ref(v_as_3551_);
    v_r_3557_ = crate::leanh::lean_box((v_res_3556_) as usize);
    return v_r_3557_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___boxed(
    mut v_x_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_x_3558_);
    v_r_3560_ = crate::leanh::lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(
    mut v_o_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_linterSets_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3564_ = lean_st_ref_get(v___y_3562_);
    v_env_3565_ = crate::leanh::lean_ctor_get(v___x_3564_, 0);
    crate::leanh::lean_inc_ref(v_env_3565_);
    crate::leanh::lean_dec(v___x_3564_);
    v___x_3566_ = l_Lean_Linter_linterSetsExt;
    v_toEnvExtension_3567_ = crate::leanh::lean_ctor_get(v___x_3566_, 0);
    v_asyncMode_3568_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3567_, 2);
    v___x_3569_ = crate::leanh::lean_box(1);
    v___x_3570_ = crate::leanh::lean_box(0);
    v_linterSets_3571_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
        v___x_3569_,
        v___x_3566_,
        v_env_3565_,
        v_asyncMode_3568_,
        v___x_3570_,
    );
    v___x_3572_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3572_, 0, v_o_3561_);
    crate::leanh::lean_ctor_set(v___x_3572_, 1, v_linterSets_3571_);
    v___x_3573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3573_, 0, v___x_3572_);
    return v___x_3573_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg___boxed(
    mut v_o_3574_: *mut crate::leanh::LeanObject,
    mut v___y_3575_: *mut crate::leanh::LeanObject,
    mut v___y_3576_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3577_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(v_o_3574_, v___y_3575_);
    crate::leanh::lean_dec(v___y_3575_);
    return v_res_3577_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
    mut v___y_3582_: *mut crate::leanh::LeanObject,
    mut v___y_3583_: *mut crate::leanh::LeanObject,
    mut v___y_3584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_options_3586_ = crate::leanh::lean_ctor_get(v___y_3583_, 2);
    crate::leanh::lean_inc_ref(v_options_3586_);
    v___x_3587_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(v_options_3586_, v___y_3584_);
    return v___x_3587_;
}
pub unsafe fn l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10___boxed(
    mut v___y_3588_: *mut crate::leanh::LeanObject,
    mut v___y_3589_: *mut crate::leanh::LeanObject,
    mut v___y_3590_: *mut crate::leanh::LeanObject,
    mut v___y_3591_: *mut crate::leanh::LeanObject,
    mut v___y_3592_: *mut crate::leanh::LeanObject,
    mut v___y_3593_: *mut crate::leanh::LeanObject,
    mut v___y_3594_: *mut crate::leanh::LeanObject,
    mut v___y_3595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3596_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
    crate::leanh::lean_dec(v___y_3594_);
    crate::leanh::lean_dec_ref(v___y_3593_);
    crate::leanh::lean_dec(v___y_3592_);
    crate::leanh::lean_dec_ref(v___y_3591_);
    crate::leanh::lean_dec(v___y_3590_);
    crate::leanh::lean_dec_ref(v___y_3589_);
    crate::leanh::lean_dec(v___y_3588_);
    return v_res_3596_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(
    mut v_opts_3597_: *mut crate::leanh::LeanObject,
    mut v_opt_3598_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_3599_ = crate::leanh::lean_ctor_get(v_opt_3598_, 0);
    v_defValue_3600_ = crate::leanh::lean_ctor_get(v_opt_3598_, 1);
    v_map_3601_ = crate::leanh::lean_ctor_get(v_opts_3597_, 0);
    v___x_3602_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_3601_,
            v_name_3599_,
        );
    if crate::leanh::lean_obj_tag(v___x_3602_) == 0 {
        let mut v___x_3603_: u8 = 0;
        v___x_3603_ = (crate::leanh::lean_unbox(v_defValue_3600_) as u8);
        return v___x_3603_;
    } else {
        let mut v_val_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_3604_ = crate::leanh::lean_ctor_get(v___x_3602_, 0);
        crate::leanh::lean_inc(v_val_3604_);
        crate::leanh::lean_dec_ref_known(v___x_3602_, 1);
        if crate::leanh::lean_obj_tag(v_val_3604_) == 1 {
            let mut v_v_3605_: u8 = 0;
            v_v_3605_ = crate::leanh::lean_ctor_get_uint8(v_val_3604_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_3604_, 0);
            return v_v_3605_;
        } else {
            let mut v___x_3606_: u8 = 0;
            crate::leanh::lean_dec(v_val_3604_);
            v___x_3606_ = (crate::leanh::lean_unbox(v_defValue_3600_) as u8);
            return v___x_3606_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22___boxed(
    mut v_opts_3607_: *mut crate::leanh::LeanObject,
    mut v_opt_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3609_: u8 = 0;
    let mut v_r_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3609_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_opts_3607_, v_opt_3608_);
    crate::leanh::lean_dec_ref(v_opt_3608_);
    crate::leanh::lean_dec_ref(v_opts_3607_);
    v_r_3610_ = crate::leanh::lean_box((v_res_3609_) as usize);
    return v_r_3610_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0(
    mut v___y_3618_: u8,
    mut v_suppressElabErrors_3619_: u8,
    mut v_x_3620_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3620_) == 1 {
        let mut v_pre_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_3621_ = crate::leanh::lean_ctor_get(v_x_3620_, 0);
        match crate::leanh::lean_obj_tag(v_pre_3621_) {
            1 => {
                let mut v_pre_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_3622_ = crate::leanh::lean_ctor_get(v_pre_3621_, 0);
                match crate::leanh::lean_obj_tag(v_pre_3622_) {
                    0 => {
                        let mut v_str_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3626_: u8 = 0;
                        v_str_3623_ = crate::leanh::lean_ctor_get(v_x_3620_, 1);
                        v_str_3624_ = crate::leanh::lean_ctor_get(v_pre_3621_, 1);
                        v___x_3625_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn___closed__5_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_;
                        v___x_3626_ = lean_string_dec_eq(v_str_3624_, v___x_3625_);
                        if v___x_3626_ == 0 {
                            let mut v___x_3627_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3628_: u8 = 0;
                            v___x_3627_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__0;
                            v___x_3628_ = lean_string_dec_eq(v_str_3624_, v___x_3627_);
                            if v___x_3628_ == 0 {
                                return v___y_3618_;
                            } else {
                                let mut v___x_3629_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3630_: u8 = 0;
                                v___x_3629_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__1;
                                v___x_3630_ = lean_string_dec_eq(v_str_3623_, v___x_3629_);
                                if v___x_3630_ == 0 {
                                    return v___y_3618_;
                                } else {
                                    return v_suppressElabErrors_3619_;
                                }
                            }
                        } else {
                            let mut v___x_3631_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3632_: u8 = 0;
                            v___x_3631_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__2;
                            v___x_3632_ = lean_string_dec_eq(v_str_3623_, v___x_3631_);
                            if v___x_3632_ == 0 {
                                return v___y_3618_;
                            } else {
                                return v_suppressElabErrors_3619_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_3633_ = crate::leanh::lean_ctor_get(v_pre_3622_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3633_) == 0 {
                            let mut v_str_3634_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3635_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3636_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3637_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3638_: u8 = 0;
                            v_str_3634_ = crate::leanh::lean_ctor_get(v_x_3620_, 1);
                            v_str_3635_ = crate::leanh::lean_ctor_get(v_pre_3621_, 1);
                            v_str_3636_ = crate::leanh::lean_ctor_get(v_pre_3622_, 1);
                            v___x_3637_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__3;
                            v___x_3638_ = lean_string_dec_eq(v_str_3636_, v___x_3637_);
                            if v___x_3638_ == 0 {
                                return v___y_3618_;
                            } else {
                                let mut v___x_3639_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3640_: u8 = 0;
                                v___x_3639_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__4;
                                v___x_3640_ = lean_string_dec_eq(v_str_3635_, v___x_3639_);
                                if v___x_3640_ == 0 {
                                    return v___y_3618_;
                                } else {
                                    let mut v___x_3641_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3642_: u8 = 0;
                                    v___x_3641_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__5;
                                    v___x_3642_ = lean_string_dec_eq(v_str_3634_, v___x_3641_);
                                    if v___x_3642_ == 0 {
                                        return v___y_3618_;
                                    } else {
                                        return v_suppressElabErrors_3619_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3618_;
                        }
                    }
                    _ => {
                        return v___y_3618_;
                    }
                }
            }
            0 => {
                let mut v_str_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3645_: u8 = 0;
                v_str_3643_ = crate::leanh::lean_ctor_get(v_x_3620_, 1);
                v___x_3644_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___closed__6;
                v___x_3645_ = lean_string_dec_eq(v_str_3643_, v___x_3644_);
                if v___x_3645_ == 0 {
                    return v___y_3618_;
                } else {
                    return v_suppressElabErrors_3619_;
                }
            }
            _ => {
                return v___y_3618_;
            }
        }
    } else {
        return v___y_3618_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___boxed(
    mut v___y_3646_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_3647_: *mut crate::leanh::LeanObject,
    mut v_x_3648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_36728__boxed_3649_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3650_: u8 = 0;
    let mut v_res_3651_: u8 = 0;
    let mut v_r_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_36728__boxed_3649_ = (crate::leanh::lean_unbox(v___y_3646_) as u8);
    v_suppressElabErrors_boxed_3650_ = (crate::leanh::lean_unbox(v_suppressElabErrors_3647_) as u8);
    v_res_3651_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0(v___y_36728__boxed_3649_, v_suppressElabErrors_boxed_3650_, v_x_3648_);
    crate::leanh::lean_dec(v_x_3648_);
    v_r_3652_ = crate::leanh::lean_box((v_res_3651_) as usize);
    return v_r_3652_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(
    mut v_msgData_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3659_ = lean_st_ref_get(v___y_3657_);
    v_env_3660_ = crate::leanh::lean_ctor_get(v___x_3659_, 0);
    crate::leanh::lean_inc_ref(v_env_3660_);
    crate::leanh::lean_dec(v___x_3659_);
    v___x_3661_ = lean_st_ref_get(v___y_3655_);
    v_mctx_3662_ = crate::leanh::lean_ctor_get(v___x_3661_, 0);
    crate::leanh::lean_inc_ref(v_mctx_3662_);
    crate::leanh::lean_dec(v___x_3661_);
    v_lctx_3663_ = crate::leanh::lean_ctor_get(v___y_3654_, 2);
    v_options_3664_ = crate::leanh::lean_ctor_get(v___y_3656_, 2);
    crate::leanh::lean_inc_ref(v_options_3664_);
    crate::leanh::lean_inc_ref(v_lctx_3663_);
    v___x_3665_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3665_, 0, v_env_3660_);
    crate::leanh::lean_ctor_set(v___x_3665_, 1, v_mctx_3662_);
    crate::leanh::lean_ctor_set(v___x_3665_, 2, v_lctx_3663_);
    crate::leanh::lean_ctor_set(v___x_3665_, 3, v_options_3664_);
    v___x_3666_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3666_, 0, v___x_3665_);
    crate::leanh::lean_ctor_set(v___x_3666_, 1, v_msgData_3653_);
    v___x_3667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3667_, 0, v___x_3666_);
    return v___x_3667_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3674_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msgData_3668_, v___y_3669_, v___y_3670_, v___y_3671_, v___y_3672_);
    crate::leanh::lean_dec(v___y_3672_);
    crate::leanh::lean_dec_ref(v___y_3671_);
    crate::leanh::lean_dec(v___y_3670_);
    crate::leanh::lean_dec_ref(v___y_3669_);
    return v_res_3674_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(
    mut v_ref_3676_: *mut crate::leanh::LeanObject,
    mut v_msgData_3677_: *mut crate::leanh::LeanObject,
    mut v_severity_3678_: u8,
    mut v_isSilent_3679_: u8,
    mut v___y_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: *mut crate::leanh::LeanObject,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: u8 = 0;
    let mut v___y_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3690_: u8 = 0;
    let mut v___y_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v___y_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3723_: u8 = 0;
    let mut v___y_3724_: u8 = 0;
    let mut v___y_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3727_: u8 = 0;
    let mut v___y_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3735_: u8 = 0;
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: u8 = 0;
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3745_: u8 = 0;
    let mut v___y_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3748_: u8 = 0;
    let mut v___y_3749_: u8 = 0;
    let mut v___y_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3752_: u8 = 0;
    let mut v___y_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: u8 = 0;
    let mut v___y_3760_: u8 = 0;
    let mut v___y_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3764_: u8 = 0;
    let mut v_ref_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: u8 = 0;
    let mut v___y_3771_: u8 = 0;
    let mut v___y_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: u8 = 0;
    let mut v___y_3777_: u8 = 0;
    let mut v___y_3779_: u8 = 0;
    let mut v_fileName_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3784_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: u8 = 0;
    let mut v___x_3789_: u8 = 0;
    let mut v___x_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3769_ = 2;
                v___x_3794_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3678_, v___x_3769_);
                if v___x_3794_ == 0 {
                    v___y_3779_ = v___x_3794_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_3677_);
                    v___x_3795_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3677_);
                    v___y_3779_ = v___x_3795_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3695_ = lean_st_ref_take(v___y_3694_);
                v_currNamespace_3696_ = crate::leanh::lean_ctor_get(v___y_3693_, 6);
                v_openDecls_3697_ = crate::leanh::lean_ctor_get(v___y_3693_, 7);
                v_env_3698_ = crate::leanh::lean_ctor_get(v___x_3695_, 0);
                v_nextMacroScope_3699_ = crate::leanh::lean_ctor_get(v___x_3695_, 1);
                v_ngen_3700_ = crate::leanh::lean_ctor_get(v___x_3695_, 2);
                v_auxDeclNGen_3701_ = crate::leanh::lean_ctor_get(v___x_3695_, 3);
                v_traceState_3702_ = crate::leanh::lean_ctor_get(v___x_3695_, 4);
                v_cache_3703_ = crate::leanh::lean_ctor_get(v___x_3695_, 5);
                v_messages_3704_ = crate::leanh::lean_ctor_get(v___x_3695_, 6);
                v_infoState_3705_ = crate::leanh::lean_ctor_get(v___x_3695_, 7);
                v_snapshotTasks_3706_ = crate::leanh::lean_ctor_get(v___x_3695_, 8);
                v_isSharedCheck_3720_ = (!crate::leanh::lean_is_exclusive(v___x_3695_)) as u8;
                if v_isSharedCheck_3720_ == 0 {
                    v___x_3708_ = v___x_3695_;
                    v_isShared_3709_ = v_isSharedCheck_3720_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3706_);
                    crate::leanh::lean_inc(v_infoState_3705_);
                    crate::leanh::lean_inc(v_messages_3704_);
                    crate::leanh::lean_inc(v_cache_3703_);
                    crate::leanh::lean_inc(v_traceState_3702_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3701_);
                    crate::leanh::lean_inc(v_ngen_3700_);
                    crate::leanh::lean_inc(v_nextMacroScope_3699_);
                    crate::leanh::lean_inc(v_env_3698_);
                    crate::leanh::lean_dec(v___x_3695_);
                    v___x_3708_ = crate::leanh::lean_box(0);
                    v_isShared_3709_ = v_isSharedCheck_3720_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_3697_);
                crate::leanh::lean_inc(v_currNamespace_3696_);
                v___x_3710_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3710_, 0, v_currNamespace_3696_);
                crate::leanh::lean_ctor_set(v___x_3710_, 1, v_openDecls_3697_);
                v___x_3711_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3711_, 0, v___x_3710_);
                crate::leanh::lean_ctor_set(v___x_3711_, 1, v___y_3688_);
                crate::leanh::lean_inc_ref(v___y_3686_);
                crate::leanh::lean_inc_ref(v___y_3692_);
                v___x_3712_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3712_, 0, v___y_3692_);
                crate::leanh::lean_ctor_set(v___x_3712_, 1, v___y_3689_);
                crate::leanh::lean_ctor_set(v___x_3712_, 2, v___y_3691_);
                crate::leanh::lean_ctor_set(v___x_3712_, 3, v___y_3686_);
                crate::leanh::lean_ctor_set(v___x_3712_, 4, v___x_3711_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3687_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3690_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3712_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3679_,
                );
                v___x_3713_ = l_Lean_MessageLog_add(v___x_3712_, v_messages_3704_);
                if v_isShared_3709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3708_, 6, v___x_3713_);
                    v___x_3715_ = v___x_3708_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_env_3698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 1, v_nextMacroScope_3699_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 2, v_ngen_3700_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 3, v_auxDeclNGen_3701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 4, v_traceState_3702_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 5, v_cache_3703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 6, v___x_3713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 7, v_infoState_3705_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 8, v_snapshotTasks_3706_);
                    v___x_3715_ = v_reuseFailAlloc_3719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3716_ = lean_st_ref_set(v___y_3694_, v___x_3715_);
                v___x_3717_ = crate::leanh::lean_box(0);
                v___x_3718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3718_, 0, v___x_3717_);
                return v___x_3718_;
            }
            4 => {
                v___x_3730_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3677_,
                    );
                v___x_3731_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v___x_3730_, v___y_3680_, v___y_3681_, v___y_3682_, v___y_3683_);
                v_a_3732_ = crate::leanh::lean_ctor_get(v___x_3731_, 0);
                v_isSharedCheck_3745_ = (!crate::leanh::lean_is_exclusive(v___x_3731_)) as u8;
                if v_isSharedCheck_3745_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    v_isShared_3735_ = v_isSharedCheck_3745_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3732_);
                    crate::leanh::lean_dec(v___x_3731_);
                    v___x_3734_ = crate::leanh::lean_box(0);
                    v_isShared_3735_ = v_isSharedCheck_3745_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_3726_, 2);
                v___x_3736_ = l_Lean_FileMap_toPosition(v___y_3726_, v___y_3725_);
                crate::leanh::lean_dec(v___y_3725_);
                v___x_3737_ = l_Lean_FileMap_toPosition(v___y_3726_, v___y_3729_);
                crate::leanh::lean_dec(v___y_3729_);
                v___x_3738_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3738_, 0, v___x_3737_);
                v___x_3739_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0;
                if v___y_3723_ == 0 {
                    crate::leanh::lean_del_object(v___x_3734_);
                    crate::leanh::lean_dec_ref(v___y_3722_);
                    v___y_3686_ = v___x_3739_;
                    v___y_3687_ = v___y_3724_;
                    v___y_3688_ = v_a_3732_;
                    v___y_3689_ = v___x_3736_;
                    v___y_3690_ = v___y_3727_;
                    v___y_3691_ = v___x_3738_;
                    v___y_3692_ = v___y_3728_;
                    v___y_3693_ = v___y_3682_;
                    v___y_3694_ = v___y_3683_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3732_);
                    v___x_3740_ = l_Lean_MessageData_hasTag(v___y_3722_, v_a_3732_);
                    if v___x_3740_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3738_, 1);
                        crate::leanh::lean_dec_ref(v___x_3736_);
                        crate::leanh::lean_dec(v_a_3732_);
                        v___x_3741_ = crate::leanh::lean_box(0);
                        if v_isShared_3735_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3734_, 0, v___x_3741_);
                            v___x_3743_ = v___x_3734_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3744_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
                            v___x_3743_ = v_reuseFailAlloc_3744_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3734_);
                        v___y_3686_ = v___x_3739_;
                        v___y_3687_ = v___y_3724_;
                        v___y_3688_ = v_a_3732_;
                        v___y_3689_ = v___x_3736_;
                        v___y_3690_ = v___y_3727_;
                        v___y_3691_ = v___x_3738_;
                        v___y_3692_ = v___y_3728_;
                        v___y_3693_ = v___y_3682_;
                        v___y_3694_ = v___y_3683_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3743_;
            }
            7 => {
                v___x_3755_ = l_Lean_Syntax_getTailPos_x3f(v___y_3751_, v___y_3748_);
                crate::leanh::lean_dec(v___y_3751_);
                if crate::leanh::lean_obj_tag(v___x_3755_) == 0 {
                    crate::leanh::lean_inc(v___y_3754_);
                    v___y_3722_ = v___y_3747_;
                    v___y_3723_ = v___y_3749_;
                    v___y_3724_ = v___y_3748_;
                    v___y_3725_ = v___y_3754_;
                    v___y_3726_ = v___y_3750_;
                    v___y_3727_ = v___y_3752_;
                    v___y_3728_ = v___y_3753_;
                    v___y_3729_ = v___y_3754_;
                    state = 4;
                    continue;
                } else {
                    v_val_3756_ = crate::leanh::lean_ctor_get(v___x_3755_, 0);
                    crate::leanh::lean_inc(v_val_3756_);
                    crate::leanh::lean_dec_ref_known(v___x_3755_, 1);
                    v___y_3722_ = v___y_3747_;
                    v___y_3723_ = v___y_3749_;
                    v___y_3724_ = v___y_3748_;
                    v___y_3725_ = v___y_3754_;
                    v___y_3726_ = v___y_3750_;
                    v___y_3727_ = v___y_3752_;
                    v___y_3728_ = v___y_3753_;
                    v___y_3729_ = v_val_3756_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3765_ = l_Lean_replaceRef(v_ref_3676_, v___y_3762_);
                v___x_3766_ = l_Lean_Syntax_getPos_x3f(v_ref_3765_, v___y_3760_);
                if crate::leanh::lean_obj_tag(v___x_3766_) == 0 {
                    v___x_3767_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3747_ = v___y_3758_;
                    v___y_3748_ = v___y_3760_;
                    v___y_3749_ = v___y_3759_;
                    v___y_3750_ = v___y_3761_;
                    v___y_3751_ = v_ref_3765_;
                    v___y_3752_ = v___y_3764_;
                    v___y_3753_ = v___y_3763_;
                    v___y_3754_ = v___x_3767_;
                    state = 7;
                    continue;
                } else {
                    v_val_3768_ = crate::leanh::lean_ctor_get(v___x_3766_, 0);
                    crate::leanh::lean_inc(v_val_3768_);
                    crate::leanh::lean_dec_ref_known(v___x_3766_, 1);
                    v___y_3747_ = v___y_3758_;
                    v___y_3748_ = v___y_3760_;
                    v___y_3749_ = v___y_3759_;
                    v___y_3750_ = v___y_3761_;
                    v___y_3751_ = v_ref_3765_;
                    v___y_3752_ = v___y_3764_;
                    v___y_3753_ = v___y_3763_;
                    v___y_3754_ = v_val_3768_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3777_ == 0 {
                    v___y_3758_ = v___y_3774_;
                    v___y_3759_ = v___y_3771_;
                    v___y_3760_ = v___y_3776_;
                    v___y_3761_ = v___y_3772_;
                    v___y_3762_ = v___y_3773_;
                    v___y_3763_ = v___y_3775_;
                    v___y_3764_ = v_severity_3678_;
                    state = 8;
                    continue;
                } else {
                    v___y_3758_ = v___y_3774_;
                    v___y_3759_ = v___y_3771_;
                    v___y_3760_ = v___y_3776_;
                    v___y_3761_ = v___y_3772_;
                    v___y_3762_ = v___y_3773_;
                    v___y_3763_ = v___y_3775_;
                    v___y_3764_ = v___x_3769_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3779_ == 0 {
                    v_fileName_3780_ = crate::leanh::lean_ctor_get(v___y_3682_, 0);
                    v_fileMap_3781_ = crate::leanh::lean_ctor_get(v___y_3682_, 1);
                    v_options_3782_ = crate::leanh::lean_ctor_get(v___y_3682_, 2);
                    v_ref_3783_ = crate::leanh::lean_ctor_get(v___y_3682_, 5);
                    v_suppressElabErrors_3784_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3682_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3785_ = crate::leanh::lean_box((v___y_3779_) as usize);
                    v___x_3786_ = crate::leanh::lean_box((v_suppressElabErrors_3784_) as usize);
                    v___f_3787_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_3787_, 0, v___x_3785_);
                    crate::leanh::lean_closure_set(v___f_3787_, 1, v___x_3786_);
                    v___x_3788_ = 1;
                    v___x_3789_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3678_, v___x_3788_);
                    if v___x_3789_ == 0 {
                        v___y_3771_ = v_suppressElabErrors_3784_;
                        v___y_3772_ = v_fileMap_3781_;
                        v___y_3773_ = v_ref_3783_;
                        v___y_3774_ = v___f_3787_;
                        v___y_3775_ = v_fileName_3780_;
                        v___y_3776_ = v___y_3779_;
                        v___y_3777_ = v___x_3789_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3790_ = l_Lean_warningAsError;
                        v___x_3791_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_3782_, v___x_3790_);
                        v___y_3771_ = v_suppressElabErrors_3784_;
                        v___y_3772_ = v_fileMap_3781_;
                        v___y_3773_ = v_ref_3783_;
                        v___y_3774_ = v___f_3787_;
                        v___y_3775_ = v_fileName_3780_;
                        v___y_3776_ = v___y_3779_;
                        v___y_3777_ = v___x_3791_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_3677_);
                    v___x_3792_ = crate::leanh::lean_box(0);
                    v___x_3793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3793_, 0, v___x_3792_);
                    return v___x_3793_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___boxed(
    mut v_ref_3796_: *mut crate::leanh::LeanObject,
    mut v_msgData_3797_: *mut crate::leanh::LeanObject,
    mut v_severity_3798_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3799_: *mut crate::leanh::LeanObject,
    mut v___y_3800_: *mut crate::leanh::LeanObject,
    mut v___y_3801_: *mut crate::leanh::LeanObject,
    mut v___y_3802_: *mut crate::leanh::LeanObject,
    mut v___y_3803_: *mut crate::leanh::LeanObject,
    mut v___y_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3805_: u8 = 0;
    let mut v_isSilent_boxed_3806_: u8 = 0;
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3805_ = (crate::leanh::lean_unbox(v_severity_3798_) as u8);
    v_isSilent_boxed_3806_ = (crate::leanh::lean_unbox(v_isSilent_3799_) as u8);
    v_res_3807_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(v_ref_3796_, v_msgData_3797_, v_severity_boxed_3805_, v_isSilent_boxed_3806_, v___y_3800_, v___y_3801_, v___y_3802_, v___y_3803_);
    crate::leanh::lean_dec(v___y_3803_);
    crate::leanh::lean_dec_ref(v___y_3802_);
    crate::leanh::lean_dec(v___y_3801_);
    crate::leanh::lean_dec_ref(v___y_3800_);
    crate::leanh::lean_dec(v_ref_3796_);
    return v_res_3807_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(
    mut v_ref_3808_: *mut crate::leanh::LeanObject,
    mut v_msgData_3809_: *mut crate::leanh::LeanObject,
    mut v___y_3810_: *mut crate::leanh::LeanObject,
    mut v___y_3811_: *mut crate::leanh::LeanObject,
    mut v___y_3812_: *mut crate::leanh::LeanObject,
    mut v___y_3813_: *mut crate::leanh::LeanObject,
    mut v___y_3814_: *mut crate::leanh::LeanObject,
    mut v___y_3815_: *mut crate::leanh::LeanObject,
    mut v___y_3816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3818_ = 1;
    v___x_3819_ = 0;
    v___x_3820_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(v_ref_3808_, v_msgData_3809_, v___x_3818_, v___x_3819_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_);
    return v___x_3820_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17___boxed(
    mut v_ref_3821_: *mut crate::leanh::LeanObject,
    mut v_msgData_3822_: *mut crate::leanh::LeanObject,
    mut v___y_3823_: *mut crate::leanh::LeanObject,
    mut v___y_3824_: *mut crate::leanh::LeanObject,
    mut v___y_3825_: *mut crate::leanh::LeanObject,
    mut v___y_3826_: *mut crate::leanh::LeanObject,
    mut v___y_3827_: *mut crate::leanh::LeanObject,
    mut v___y_3828_: *mut crate::leanh::LeanObject,
    mut v___y_3829_: *mut crate::leanh::LeanObject,
    mut v___y_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3831_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(v_ref_3821_, v_msgData_3822_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
    crate::leanh::lean_dec(v___y_3829_);
    crate::leanh::lean_dec_ref(v___y_3828_);
    crate::leanh::lean_dec(v___y_3827_);
    crate::leanh::lean_dec_ref(v___y_3826_);
    crate::leanh::lean_dec(v___y_3825_);
    crate::leanh::lean_dec_ref(v___y_3824_);
    crate::leanh::lean_dec(v___y_3823_);
    crate::leanh::lean_dec(v_ref_3821_);
    return v_res_3831_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3833_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__0;
    v___x_3834_ = l_Lean_stringToMessageData(v___x_3833_);
    return v___x_3834_;
}
pub unsafe fn _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3836_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__2;
    v___x_3837_ = l_Lean_stringToMessageData(v___x_3836_);
    return v___x_3837_;
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(
    mut v_linterOption_3838_: *mut crate::leanh::LeanObject,
    mut v_stx_3839_: *mut crate::leanh::LeanObject,
    mut v_msg_3840_: *mut crate::leanh::LeanObject,
    mut v___y_3841_: *mut crate::leanh::LeanObject,
    mut v___y_3842_: *mut crate::leanh::LeanObject,
    mut v___y_3843_: *mut crate::leanh::LeanObject,
    mut v___y_3844_: *mut crate::leanh::LeanObject,
    mut v___y_3845_: *mut crate::leanh::LeanObject,
    mut v___y_3846_: *mut crate::leanh::LeanObject,
    mut v___y_3847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_name_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3852_: u8 = 0;
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_disable_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3866_: u8 = 0;
    let mut v_unused_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_name_3849_ = crate::leanh::lean_ctor_get(v_linterOption_3838_, 0);
                v_isSharedCheck_3866_ =
                    (!crate::leanh::lean_is_exclusive(v_linterOption_3838_)) as u8;
                if v_isSharedCheck_3866_ == 0 {
                    v_unused_3867_ = crate::leanh::lean_ctor_get(v_linterOption_3838_, 1);
                    crate::leanh::lean_dec(v_unused_3867_);
                    v___x_3851_ = v_linterOption_3838_;
                    v_isShared_3852_ = v_isSharedCheck_3866_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_name_3849_);
                    crate::leanh::lean_dec(v_linterOption_3838_);
                    v___x_3851_ = crate::leanh::lean_box(0);
                    v_isShared_3852_ = v_isSharedCheck_3866_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3853_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__1);
                crate::leanh::lean_inc(v_name_3849_);
                v___x_3854_ = l_Lean_MessageData_ofName(v_name_3849_);
                if v_isShared_3852_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3851_, 7);
                    crate::leanh::lean_ctor_set(v___x_3851_, 1, v___x_3854_);
                    crate::leanh::lean_ctor_set(v___x_3851_, 0, v___x_3853_);
                    v___x_3856_ = v___x_3851_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3865_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3865_, 1, v___x_3854_);
                    v___x_3856_ = v_reuseFailAlloc_3865_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3857_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3), core::ptr::addr_of_mut!(l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3_once), _init_l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___closed__3);
                v___x_3858_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3858_, 0, v___x_3856_);
                crate::leanh::lean_ctor_set(v___x_3858_, 1, v___x_3857_);
                v_disable_3859_ = l_Lean_MessageData_note(v___x_3858_);
                v___x_3860_ = l_Lean_Linter_linterMessageTag;
                v___x_3861_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3861_, 0, v_msg_3840_);
                crate::leanh::lean_ctor_set(v___x_3861_, 1, v_disable_3859_);
                v___x_3862_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3862_, 0, v___x_3860_);
                crate::leanh::lean_ctor_set(v___x_3862_, 1, v___x_3861_);
                v___x_3863_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3863_, 0, v_name_3849_);
                crate::leanh::lean_ctor_set(v___x_3863_, 1, v___x_3862_);
                v___x_3864_ = l_Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17(v_stx_3839_, v___x_3863_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
                return v___x_3864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11___boxed(
    mut v_linterOption_3868_: *mut crate::leanh::LeanObject,
    mut v_stx_3869_: *mut crate::leanh::LeanObject,
    mut v_msg_3870_: *mut crate::leanh::LeanObject,
    mut v___y_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
    mut v___y_3876_: *mut crate::leanh::LeanObject,
    mut v___y_3877_: *mut crate::leanh::LeanObject,
    mut v___y_3878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3879_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(v_linterOption_3868_, v_stx_3869_, v_msg_3870_, v___y_3871_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
    crate::leanh::lean_dec(v___y_3877_);
    crate::leanh::lean_dec_ref(v___y_3876_);
    crate::leanh::lean_dec(v___y_3875_);
    crate::leanh::lean_dec_ref(v___y_3874_);
    crate::leanh::lean_dec(v___y_3873_);
    crate::leanh::lean_dec_ref(v___y_3872_);
    crate::leanh::lean_dec(v___y_3871_);
    crate::leanh::lean_dec(v_stx_3869_);
    return v_res_3879_;
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(
    mut v_linterOption_3880_: *mut crate::leanh::LeanObject,
    mut v_stx_3881_: *mut crate::leanh::LeanObject,
    mut v_msg_3882_: *mut crate::leanh::LeanObject,
    mut v___y_3883_: *mut crate::leanh::LeanObject,
    mut v___y_3884_: *mut crate::leanh::LeanObject,
    mut v___y_3885_: *mut crate::leanh::LeanObject,
    mut v___y_3886_: *mut crate::leanh::LeanObject,
    mut v___y_3887_: *mut crate::leanh::LeanObject,
    mut v___y_3888_: *mut crate::leanh::LeanObject,
    mut v___y_3889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3896_: u8 = 0;
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3891_ = l_Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10(v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
                v_a_3892_ = crate::leanh::lean_ctor_get(v___x_3891_, 0);
                v_isSharedCheck_3902_ = (!crate::leanh::lean_is_exclusive(v___x_3891_)) as u8;
                if v_isSharedCheck_3902_ == 0 {
                    v___x_3894_ = v___x_3891_;
                    v_isShared_3895_ = v_isSharedCheck_3902_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3892_);
                    crate::leanh::lean_dec(v___x_3891_);
                    v___x_3894_ = crate::leanh::lean_box(0);
                    v_isShared_3895_ = v_isSharedCheck_3902_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3896_ = l_Lean_Linter_getLinterValue(v_linterOption_3880_, v_a_3892_);
                crate::leanh::lean_dec(v_a_3892_);
                if v___x_3896_ == 0 {
                    crate::leanh::lean_dec_ref(v_msg_3882_);
                    crate::leanh::lean_dec_ref(v_linterOption_3880_);
                    v___x_3897_ = crate::leanh::lean_box(0);
                    if v_isShared_3895_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3894_, 0, v___x_3897_);
                        v___x_3899_ = v___x_3894_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3897_);
                        v___x_3899_ = v_reuseFailAlloc_3900_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3894_);
                    v___x_3901_ = l_Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11(v_linterOption_3880_, v_stx_3881_, v_msg_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_, v___y_3888_, v___y_3889_);
                    return v___x_3901_;
                }
            }
            2 => {
                return v___x_3899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2___boxed(
    mut v_linterOption_3903_: *mut crate::leanh::LeanObject,
    mut v_stx_3904_: *mut crate::leanh::LeanObject,
    mut v_msg_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
    mut v___y_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v___y_3909_: *mut crate::leanh::LeanObject,
    mut v___y_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
    mut v___y_3912_: *mut crate::leanh::LeanObject,
    mut v___y_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3914_ = l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(
        v_linterOption_3903_,
        v_stx_3904_,
        v_msg_3905_,
        v___y_3906_,
        v___y_3907_,
        v___y_3908_,
        v___y_3909_,
        v___y_3910_,
        v___y_3911_,
        v___y_3912_,
    );
    crate::leanh::lean_dec(v___y_3912_);
    crate::leanh::lean_dec_ref(v___y_3911_);
    crate::leanh::lean_dec(v___y_3910_);
    crate::leanh::lean_dec_ref(v___y_3909_);
    crate::leanh::lean_dec(v___y_3908_);
    crate::leanh::lean_dec_ref(v___y_3907_);
    crate::leanh::lean_dec(v___y_3906_);
    crate::leanh::lean_dec(v_stx_3904_);
    return v_res_3914_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3915_ = crate::leanh::lean_box(0);
    v___x_3916_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_3917_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3917_, 0, v___x_3916_);
    crate::leanh::lean_ctor_set(v___x_3917_, 1, v___x_3915_);
    return v___x_3917_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3919_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___closed__0);
    v___x_3920_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3920_, 0, v___x_3919_);
    return v___x_3920_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg___boxed(
    mut v___y_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3922_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
    return v_res_3922_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(
    mut v_currNamespace_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
    mut v___y_3925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3926_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3926_, 0, v_currNamespace_3923_);
    crate::leanh::lean_ctor_set(v___x_3926_, 1, v___y_3925_);
    return v___x_3926_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed(
    mut v_currNamespace_3927_: *mut crate::leanh::LeanObject,
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v___y_3929_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3930_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3(
            v_currNamespace_3927_,
            v___y_3928_,
            v___y_3929_,
        );
    crate::leanh::lean_dec_ref(v___y_3928_);
    return v_res_3930_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0()
-> f64 {
    let mut v___x_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: f64 = 0.0;
    v___x_3931_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3932_ = lean_float_of_nat(v___x_3931_);
    return v___x_3932_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(
    mut v_cls_3935_: *mut crate::leanh::LeanObject,
    mut v_msg_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
    mut v___y_3938_: *mut crate::leanh::LeanObject,
    mut v___y_3939_: *mut crate::leanh::LeanObject,
    mut v___y_3940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3947_: u8 = 0;
    let mut v___x_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3960_: u8 = 0;
    let mut v_tid_3961_: u64 = 0;
    let mut v_traces_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3965_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: f64 = 0.0;
    let mut v___x_3968_: u8 = 0;
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3986_: u8 = 0;
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3942_ = crate::leanh::lean_ctor_get(v___y_3939_, 5);
                v___x_3943_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msg_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
                v_a_3944_ = crate::leanh::lean_ctor_get(v___x_3943_, 0);
                v_isSharedCheck_3988_ = (!crate::leanh::lean_is_exclusive(v___x_3943_)) as u8;
                if v_isSharedCheck_3988_ == 0 {
                    v___x_3946_ = v___x_3943_;
                    v_isShared_3947_ = v_isSharedCheck_3988_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3944_);
                    crate::leanh::lean_dec(v___x_3943_);
                    v___x_3946_ = crate::leanh::lean_box(0);
                    v_isShared_3947_ = v_isSharedCheck_3988_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3948_ = lean_st_ref_take(v___y_3940_);
                v_traceState_3949_ = crate::leanh::lean_ctor_get(v___x_3948_, 4);
                v_env_3950_ = crate::leanh::lean_ctor_get(v___x_3948_, 0);
                v_nextMacroScope_3951_ = crate::leanh::lean_ctor_get(v___x_3948_, 1);
                v_ngen_3952_ = crate::leanh::lean_ctor_get(v___x_3948_, 2);
                v_auxDeclNGen_3953_ = crate::leanh::lean_ctor_get(v___x_3948_, 3);
                v_cache_3954_ = crate::leanh::lean_ctor_get(v___x_3948_, 5);
                v_messages_3955_ = crate::leanh::lean_ctor_get(v___x_3948_, 6);
                v_infoState_3956_ = crate::leanh::lean_ctor_get(v___x_3948_, 7);
                v_snapshotTasks_3957_ = crate::leanh::lean_ctor_get(v___x_3948_, 8);
                v_isSharedCheck_3987_ = (!crate::leanh::lean_is_exclusive(v___x_3948_)) as u8;
                if v_isSharedCheck_3987_ == 0 {
                    v___x_3959_ = v___x_3948_;
                    v_isShared_3960_ = v_isSharedCheck_3987_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3957_);
                    crate::leanh::lean_inc(v_infoState_3956_);
                    crate::leanh::lean_inc(v_messages_3955_);
                    crate::leanh::lean_inc(v_cache_3954_);
                    crate::leanh::lean_inc(v_traceState_3949_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3953_);
                    crate::leanh::lean_inc(v_ngen_3952_);
                    crate::leanh::lean_inc(v_nextMacroScope_3951_);
                    crate::leanh::lean_inc(v_env_3950_);
                    crate::leanh::lean_dec(v___x_3948_);
                    v___x_3959_ = crate::leanh::lean_box(0);
                    v_isShared_3960_ = v_isSharedCheck_3987_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3961_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3949_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3962_ = crate::leanh::lean_ctor_get(v_traceState_3949_, 0);
                v_isSharedCheck_3986_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3949_)) as u8;
                if v_isSharedCheck_3986_ == 0 {
                    v___x_3964_ = v_traceState_3949_;
                    v_isShared_3965_ = v_isSharedCheck_3986_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3962_);
                    crate::leanh::lean_dec(v_traceState_3949_);
                    v___x_3964_ = crate::leanh::lean_box(0);
                    v_isShared_3965_ = v_isSharedCheck_3986_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3966_ = crate::leanh::lean_box(0);
                v___x_3967_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__0);
                v___x_3968_ = 0;
                v___x_3969_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0;
                v___x_3970_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3970_, 0, v_cls_3935_);
                crate::leanh::lean_ctor_set(v___x_3970_, 1, v___x_3966_);
                crate::leanh::lean_ctor_set(v___x_3970_, 2, v___x_3969_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3970_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3967_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3970_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3967_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3970_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3968_,
                );
                v___x_3971_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1;
                v___x_3972_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3972_, 0, v___x_3970_);
                crate::leanh::lean_ctor_set(v___x_3972_, 1, v_a_3944_);
                crate::leanh::lean_ctor_set(v___x_3972_, 2, v___x_3971_);
                crate::leanh::lean_inc(v_ref_3942_);
                v___x_3973_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3973_, 0, v_ref_3942_);
                crate::leanh::lean_ctor_set(v___x_3973_, 1, v___x_3972_);
                v___x_3974_ = l_Lean_PersistentArray_push___redArg(v_traces_3962_, v___x_3973_);
                if v_isShared_3965_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3964_, 0, v___x_3974_);
                    v___x_3976_ = v___x_3964_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3985_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3985_, 0, v___x_3974_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3961_,
                    );
                    v___x_3976_ = v_reuseFailAlloc_3985_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3960_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3959_, 4, v___x_3976_);
                    v___x_3978_ = v___x_3959_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3984_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_env_3950_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 1, v_nextMacroScope_3951_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 2, v_ngen_3952_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 3, v_auxDeclNGen_3953_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 4, v___x_3976_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 5, v_cache_3954_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 6, v_messages_3955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 7, v_infoState_3956_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 8, v_snapshotTasks_3957_);
                    v___x_3978_ = v_reuseFailAlloc_3984_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3979_ = lean_st_ref_set(v___y_3940_, v___x_3978_);
                v___x_3980_ = crate::leanh::lean_box(0);
                if v_isShared_3947_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3946_, 0, v___x_3980_);
                    v___x_3982_ = v___x_3946_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3983_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3980_);
                    v___x_3982_ = v_reuseFailAlloc_3983_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3982_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___boxed(
    mut v_cls_3989_: *mut crate::leanh::LeanObject,
    mut v_msg_3990_: *mut crate::leanh::LeanObject,
    mut v___y_3991_: *mut crate::leanh::LeanObject,
    mut v___y_3992_: *mut crate::leanh::LeanObject,
    mut v___y_3993_: *mut crate::leanh::LeanObject,
    mut v___y_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3996_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_3989_, v_msg_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
    crate::leanh::lean_dec(v___y_3994_);
    crate::leanh::lean_dec_ref(v___y_3993_);
    crate::leanh::lean_dec(v___y_3992_);
    crate::leanh::lean_dec_ref(v___y_3991_);
    return v_res_3996_;
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(
    mut v_as_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
    mut v___y_4002_: *mut crate::leanh::LeanObject,
    mut v___y_4003_: *mut crate::leanh::LeanObject,
    mut v___y_4004_: *mut crate::leanh::LeanObject,
    mut v___y_4005_: *mut crate::leanh::LeanObject,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4011_: u8 = 0;
    let mut v_tail_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_3999_) == 0 {
                    v___x_4008_ = crate::leanh::lean_box(0);
                    v___x_4009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4009_, 0, v___x_4008_);
                    return v___x_4009_;
                } else {
                    v_options_4010_ = crate::leanh::lean_ctor_get(v___y_4005_, 2);
                    v_hasTrace_4011_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4010_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4011_ == 0 {
                        v_tail_4012_ = crate::leanh::lean_ctor_get(v_as_3999_, 1);
                        crate::leanh::lean_inc(v_tail_4012_);
                        crate::leanh::lean_dec_ref_known(v_as_3999_, 2);
                        v_as_3999_ = v_tail_4012_;
                        state = 0;
                        continue;
                    } else {
                        v_head_4014_ = crate::leanh::lean_ctor_get(v_as_3999_, 0);
                        crate::leanh::lean_inc(v_head_4014_);
                        v_tail_4015_ = crate::leanh::lean_ctor_get(v_as_3999_, 1);
                        crate::leanh::lean_inc(v_tail_4015_);
                        crate::leanh::lean_dec_ref_known(v_as_3999_, 2);
                        v_fst_4016_ = crate::leanh::lean_ctor_get(v_head_4014_, 0);
                        crate::leanh::lean_inc_n(v_fst_4016_, 2);
                        v_snd_4017_ = crate::leanh::lean_ctor_get(v_head_4014_, 1);
                        crate::leanh::lean_inc(v_snd_4017_);
                        crate::leanh::lean_dec(v_head_4014_);
                        v_inheritedTraceOptions_4018_ =
                            crate::leanh::lean_ctor_get(v___y_4005_, 13);
                        v___x_4019_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0;
                        v___x_4020_ = l_Lean_Name_append(v___x_4019_, v_fst_4016_);
                        v___x_4021_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4018_,
                            v_options_4010_,
                            v___x_4020_,
                        );
                        crate::leanh::lean_dec(v___x_4020_);
                        if v___x_4021_ == 0 {
                            crate::leanh::lean_dec(v_snd_4017_);
                            crate::leanh::lean_dec(v_fst_4016_);
                            v_as_3999_ = v_tail_4015_;
                            state = 0;
                            continue;
                        } else {
                            v___x_4023_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4023_, 0, v_snd_4017_);
                            v___x_4024_ = l_Lean_MessageData_ofFormat(v___x_4023_);
                            v___x_4025_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_fst_4016_, v___x_4024_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_);
                            if crate::leanh::lean_obj_tag(v___x_4025_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4025_, 1);
                                v_as_3999_ = v_tail_4015_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_tail_4015_);
                                return v___x_4025_;
                            }
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___boxed(
    mut v_as_4027_: *mut crate::leanh::LeanObject,
    mut v___y_4028_: *mut crate::leanh::LeanObject,
    mut v___y_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4036_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v_as_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
    crate::leanh::lean_dec(v___y_4034_);
    crate::leanh::lean_dec_ref(v___y_4033_);
    crate::leanh::lean_dec(v___y_4032_);
    crate::leanh::lean_dec_ref(v___y_4031_);
    crate::leanh::lean_dec(v___y_4030_);
    crate::leanh::lean_dec_ref(v___y_4029_);
    crate::leanh::lean_dec(v___y_4028_);
    return v_res_4036_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(
    mut v_env_4037_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4038_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4039_: *mut crate::leanh::LeanObject,
    mut v_n_4040_: *mut crate::leanh::LeanObject,
    mut v___y_4041_: *mut crate::leanh::LeanObject,
    mut v___y_4042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ = l_Lean_ResolveName_resolveNamespace(
        v_env_4037_,
        v_currNamespace_4038_,
        v_openDecls_4039_,
        v_n_4040_,
    );
    v___x_4044_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4044_, 0, v___x_4043_);
    crate::leanh::lean_ctor_set(v___x_4044_, 1, v___y_4042_);
    return v___x_4044_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed(
    mut v_env_4045_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4046_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4047_: *mut crate::leanh::LeanObject,
    mut v_n_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4051_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2(
            v_env_4045_,
            v_currNamespace_4046_,
            v_openDecls_4047_,
            v_n_4048_,
            v___y_4049_,
            v___y_4050_,
        );
    crate::leanh::lean_dec_ref(v___y_4049_);
    return v_res_4051_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(
    mut v_env_4052_: *mut crate::leanh::LeanObject,
    mut v_declName_4053_: *mut crate::leanh::LeanObject,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: u8 = 0;
    let mut v_env_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: u8 = 0;
    let mut v___x_4060_: u8 = 0;
    v___x_4056_ = 0;
    v_env_4057_ = l_Lean_Environment_setExporting(v_env_4052_, v___x_4056_);
    crate::leanh::lean_inc(v_declName_4053_);
    v___x_4058_ = l_Lean_mkPrivateName(v_env_4057_, v_declName_4053_);
    v___x_4059_ = 1;
    crate::leanh::lean_inc_ref(v_env_4057_);
    v___x_4060_ = l_Lean_Environment_contains(v_env_4057_, v___x_4058_, v___x_4059_);
    if v___x_4060_ == 0 {
        let mut v___x_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4062_: u8 = 0;
        let mut v___x_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4061_ = l_Lean_privateToUserName(v_declName_4053_);
        v___x_4062_ = l_Lean_Environment_contains(v_env_4057_, v___x_4061_, v___x_4059_);
        v___x_4063_ = crate::leanh::lean_box((v___x_4062_) as usize);
        v___x_4064_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4064_, 0, v___x_4063_);
        crate::leanh::lean_ctor_set(v___x_4064_, 1, v___y_4055_);
        return v___x_4064_;
    } else {
        let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_env_4057_);
        crate::leanh::lean_dec(v_declName_4053_);
        v___x_4065_ = crate::leanh::lean_box((v___x_4060_) as usize);
        v___x_4066_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4066_, 0, v___x_4065_);
        crate::leanh::lean_ctor_set(v___x_4066_, 1, v___y_4055_);
        return v___x_4066_;
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed(
    mut v_env_4067_: *mut crate::leanh::LeanObject,
    mut v_declName_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4071_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1(
            v_env_4067_,
            v_declName_4068_,
            v___y_4069_,
            v___y_4070_,
        );
    crate::leanh::lean_dec_ref(v___y_4069_);
    return v_res_4071_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(
    mut v_keys_4072_: *mut crate::leanh::LeanObject,
    mut v_i_4073_: *mut crate::leanh::LeanObject,
    mut v_k_4074_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u8 = 0;
    let mut v_k_x27_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4075_ = lean_array_get_size(v_keys_4072_);
                v___x_4076_ = lean_nat_dec_lt(v_i_4073_, v___x_4075_);
                if v___x_4076_ == 0 {
                    crate::leanh::lean_dec(v_i_4073_);
                    return v___x_4076_;
                } else {
                    v_k_x27_4077_ = lean_array_fget_borrowed(v_keys_4072_, v_i_4073_);
                    v___x_4078_ = l_Lean_instBEqExtraModUse_beq(v_k_4074_, v_k_x27_4077_);
                    if v___x_4078_ == 0 {
                        v___x_4079_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4080_ = lean_nat_add(v_i_4073_, v___x_4079_);
                        crate::leanh::lean_dec(v_i_4073_);
                        v_i_4073_ = v___x_4080_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4073_);
                        return v___x_4078_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg___boxed(
    mut v_keys_4082_: *mut crate::leanh::LeanObject,
    mut v_i_4083_: *mut crate::leanh::LeanObject,
    mut v_k_4084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4085_: u8 = 0;
    let mut v_r_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(v_keys_4082_, v_i_4083_, v_k_4084_);
    crate::leanh::lean_dec_ref(v_k_4084_);
    crate::leanh::lean_dec_ref(v_keys_4082_);
    v_r_4086_ = crate::leanh::lean_box((v_res_4085_) as usize);
    return v_r_4086_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__0()
-> usize {
    let mut v___x_4087_: usize = 0;
    let mut v___x_4088_: usize = 0;
    let mut v___x_4089_: usize = 0;
    v___x_4087_ = 5usize;
    v___x_4088_ = 1usize;
    v___x_4089_ = lean_usize_shift_left(v___x_4088_, v___x_4087_);
    return v___x_4089_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__1()
-> usize {
    let mut v___x_4090_: usize = 0;
    let mut v___x_4091_: usize = 0;
    let mut v___x_4092_: usize = 0;
    v___x_4090_ = 1usize;
    v___x_4091_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__0);
    v___x_4092_ = lean_usize_sub(v___x_4091_, v___x_4090_);
    return v___x_4092_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(
    mut v_x_4093_: *mut crate::leanh::LeanObject,
    mut v_x_4094_: usize,
    mut v_x_4095_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: usize = 0;
    let mut v___x_4099_: usize = 0;
    let mut v___x_4100_: usize = 0;
    let mut v_j_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v_node_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: usize = 0;
    let mut v___x_4108_: u8 = 0;
    let mut v_ks_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4093_) == 0 {
                    v_es_4096_ = crate::leanh::lean_ctor_get(v_x_4093_, 0);
                    v___x_4097_ = crate::leanh::lean_box(2);
                    v___x_4098_ = 5usize;
                    v___x_4099_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___closed__1);
                    v___x_4100_ = lean_usize_land(v_x_4094_, v___x_4099_);
                    v_j_4101_ = lean_usize_to_nat(v___x_4100_);
                    v___x_4102_ = lean_array_get_borrowed(v___x_4097_, v_es_4096_, v_j_4101_);
                    crate::leanh::lean_dec(v_j_4101_);
                    match crate::leanh::lean_obj_tag(v___x_4102_) {
                        0 => {
                            v_key_4103_ = crate::leanh::lean_ctor_get(v___x_4102_, 0);
                            v___x_4104_ = l_Lean_instBEqExtraModUse_beq(v_x_4095_, v_key_4103_);
                            return v___x_4104_;
                        }
                        1 => {
                            v_node_4105_ = crate::leanh::lean_ctor_get(v___x_4102_, 0);
                            v___x_4106_ = lean_usize_shift_right(v_x_4094_, v___x_4098_);
                            v_x_4093_ = v_node_4105_;
                            v_x_4094_ = v___x_4106_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4108_ = 0;
                            return v___x_4108_;
                        }
                    }
                } else {
                    v_ks_4109_ = crate::leanh::lean_ctor_get(v_x_4093_, 0);
                    v___x_4110_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4111_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(v_ks_4109_, v___x_4110_, v_x_4095_);
                    return v___x_4111_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg___boxed(
    mut v_x_4112_: *mut crate::leanh::LeanObject,
    mut v_x_4113_: *mut crate::leanh::LeanObject,
    mut v_x_4114_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37435__boxed_4115_: usize = 0;
    let mut v_res_4116_: u8 = 0;
    let mut v_r_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37435__boxed_4115_ = crate::leanh::lean_unbox_usize(v_x_4113_);
    crate::leanh::lean_dec(v_x_4113_);
    v_res_4116_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(v_x_4112_, v_x_37435__boxed_4115_, v_x_4114_);
    crate::leanh::lean_dec_ref(v_x_4114_);
    crate::leanh::lean_dec_ref(v_x_4112_);
    v_r_4117_ = crate::leanh::lean_box((v_res_4116_) as usize);
    return v_r_4117_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(
    mut v_x_4118_: *mut crate::leanh::LeanObject,
    mut v_x_4119_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4120_: u64 = 0;
    let mut v___x_4121_: usize = 0;
    let mut v___x_4122_: u8 = 0;
    v___x_4120_ = l_Lean_instHashableExtraModUse_hash(v_x_4119_);
    v___x_4121_ = lean_uint64_to_usize(v___x_4120_);
    v___x_4122_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(v_x_4118_, v___x_4121_, v_x_4119_);
    return v___x_4122_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg___boxed(
    mut v_x_4123_: *mut crate::leanh::LeanObject,
    mut v_x_4124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4125_: u8 = 0;
    let mut v_r_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4125_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(v_x_4123_, v_x_4124_);
    crate::leanh::lean_dec_ref(v_x_4124_);
    crate::leanh::lean_dec_ref(v_x_4123_);
    v_r_4126_ = crate::leanh::lean_box((v_res_4125_) as usize);
    return v_r_4126_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4129_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__1;
    v___x_4130_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__0;
    v___x_4131_ = l_Lean_PersistentHashMap_empty(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4130_,
        v___x_4129_,
    );
    return v___x_4131_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4132_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4132_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4133_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__3);
    v___x_4134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4134_, 0, v___x_4133_);
    return v___x_4134_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4135_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4);
    v___x_4136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4136_, 0, v___x_4135_);
    crate::leanh::lean_ctor_set(v___x_4136_, 1, v___x_4135_);
    return v___x_4136_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4137_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__4);
    v___x_4138_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4138_, 0, v___x_4137_);
    crate::leanh::lean_ctor_set(v___x_4138_, 1, v___x_4137_);
    crate::leanh::lean_ctor_set(v___x_4138_, 2, v___x_4137_);
    crate::leanh::lean_ctor_set(v___x_4138_, 3, v___x_4137_);
    crate::leanh::lean_ctor_set(v___x_4138_, 4, v___x_4137_);
    crate::leanh::lean_ctor_set(v___x_4138_, 5, v___x_4137_);
    return v___x_4138_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4143_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__9;
    v___x_4144_ = l_Lean_stringToMessageData(v___x_4143_);
    return v___x_4144_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4146_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__11;
    v___x_4147_ = l_Lean_stringToMessageData(v___x_4146_);
    return v___x_4147_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4148_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg___closed__0;
    v___x_4149_ = l_Lean_stringToMessageData(v___x_4148_);
    return v___x_4149_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v_cls_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cls_4150_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8;
    v___x_4151_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4___closed__0;
    v___x_4152_ = l_Lean_Name_append(v___x_4151_, v_cls_4150_);
    return v___x_4152_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__15;
    v___x_4155_ = l_Lean_stringToMessageData(v___x_4154_);
    return v___x_4155_;
}
pub unsafe fn _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4157_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__17;
    v___x_4158_ = l_Lean_stringToMessageData(v___x_4157_);
    return v___x_4158_;
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(
    mut v_mod_4163_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4164_: u8,
    mut v_hint_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
    mut v___y_4169_: *mut crate::leanh::LeanObject,
    mut v___y_4170_: *mut crate::leanh::LeanObject,
    mut v___y_4171_: *mut crate::leanh::LeanObject,
    mut v___y_4172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4176_: u8 = 0;
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v_asyncMode_4200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4221_: u8 = 0;
    let mut v_unused_4222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4224_: u8 = 0;
    let mut v_unused_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: u8 = 0;
    let mut v_options_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4229_: u8 = 0;
    let mut v_inheritedTraceOptions_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cls_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: u8 = 0;
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4174_ = lean_st_ref_get(v___y_4172_);
                v_env_4175_ = crate::leanh::lean_ctor_get(v___x_4174_, 0);
                crate::leanh::lean_inc_ref(v_env_4175_);
                crate::leanh::lean_dec(v___x_4174_);
                v_isExporting_4176_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4175_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4175_);
                v___x_4177_ = lean_st_ref_get(v___y_4172_);
                v_env_4178_ = crate::leanh::lean_ctor_get(v___x_4177_, 0);
                crate::leanh::lean_inc_ref(v_env_4178_);
                crate::leanh::lean_dec(v___x_4177_);
                v___x_4179_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__2);
                crate::leanh::lean_inc(v_mod_4163_);
                v_entry_4180_ = crate::leanh::lean_alloc_ctor(0, 1, (2) as u32);
                crate::leanh::lean_ctor_set(v_entry_4180_, 0, v_mod_4163_);
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4180_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_isExporting_4176_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v_entry_4180_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1 + 1) as u32,
                    v_isMeta_4164_,
                );
                v___x_4181_ = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
                v___x_4182_ = crate::leanh::lean_box(1);
                v___x_4183_ = crate::leanh::lean_box(0);
                v___x_4226_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4179_,
                    v___x_4181_,
                    v_env_4178_,
                    v___x_4182_,
                    v___x_4183_,
                );
                v___x_4227_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(v___x_4226_, v_entry_4180_);
                crate::leanh::lean_dec(v___x_4226_);
                if v___x_4227_ == 0 {
                    v_options_4228_ = crate::leanh::lean_ctor_get(v___y_4171_, 2);
                    v_hasTrace_4229_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4228_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4229_ == 0 {
                        crate::leanh::lean_dec(v_hint_4165_);
                        crate::leanh::lean_dec(v_mod_4163_);
                        v___y_4185_ = v___y_4170_;
                        v___y_4186_ = v___y_4172_;
                        state = 1;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4230_ =
                            crate::leanh::lean_ctor_get(v___y_4171_, 13);
                        v_cls_4231_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__8;
                        v___x_4251_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__14);
                        v___x_4252_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4230_,
                            v_options_4228_,
                            v___x_4251_,
                        );
                        if v___x_4252_ == 0 {
                            crate::leanh::lean_dec(v_hint_4165_);
                            crate::leanh::lean_dec(v_mod_4163_);
                            v___y_4185_ = v___y_4170_;
                            v___y_4186_ = v___y_4172_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4253_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__16);
                            if v_isExporting_4176_ == 0 {
                                v___x_4262_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__21;
                                v___y_4255_ = v___x_4262_;
                                state = 8;
                                continue;
                            } else {
                                v___x_4263_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__22;
                                v___y_4255_ = v___x_4263_;
                                state = 8;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4180_, 1);
                    crate::leanh::lean_dec(v_hint_4165_);
                    crate::leanh::lean_dec(v_mod_4163_);
                    v___x_4264_ = crate::leanh::lean_box(0);
                    v___x_4265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4265_, 0, v___x_4264_);
                    return v___x_4265_;
                }
            }
            1 => {
                v___x_4187_ = lean_st_ref_take(v___y_4186_);
                v_toEnvExtension_4188_ = crate::leanh::lean_ctor_get(v___x_4181_, 0);
                v_env_4189_ = crate::leanh::lean_ctor_get(v___x_4187_, 0);
                v_nextMacroScope_4190_ = crate::leanh::lean_ctor_get(v___x_4187_, 1);
                v_ngen_4191_ = crate::leanh::lean_ctor_get(v___x_4187_, 2);
                v_auxDeclNGen_4192_ = crate::leanh::lean_ctor_get(v___x_4187_, 3);
                v_traceState_4193_ = crate::leanh::lean_ctor_get(v___x_4187_, 4);
                v_messages_4194_ = crate::leanh::lean_ctor_get(v___x_4187_, 6);
                v_infoState_4195_ = crate::leanh::lean_ctor_get(v___x_4187_, 7);
                v_snapshotTasks_4196_ = crate::leanh::lean_ctor_get(v___x_4187_, 8);
                v_isSharedCheck_4224_ = (!crate::leanh::lean_is_exclusive(v___x_4187_)) as u8;
                if v_isSharedCheck_4224_ == 0 {
                    v_unused_4225_ = crate::leanh::lean_ctor_get(v___x_4187_, 5);
                    crate::leanh::lean_dec(v_unused_4225_);
                    v___x_4198_ = v___x_4187_;
                    v_isShared_4199_ = v_isSharedCheck_4224_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4196_);
                    crate::leanh::lean_inc(v_infoState_4195_);
                    crate::leanh::lean_inc(v_messages_4194_);
                    crate::leanh::lean_inc(v_traceState_4193_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4192_);
                    crate::leanh::lean_inc(v_ngen_4191_);
                    crate::leanh::lean_inc(v_nextMacroScope_4190_);
                    crate::leanh::lean_inc(v_env_4189_);
                    crate::leanh::lean_dec(v___x_4187_);
                    v___x_4198_ = crate::leanh::lean_box(0);
                    v_isShared_4199_ = v_isSharedCheck_4224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_4200_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4188_, 2);
                v___x_4201_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_4181_,
                    v_env_4189_,
                    v_entry_4180_,
                    v_asyncMode_4200_,
                    v___x_4183_,
                );
                v___x_4202_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__5);
                if v_isShared_4199_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4198_, 5, v___x_4202_);
                    crate::leanh::lean_ctor_set(v___x_4198_, 0, v___x_4201_);
                    v___x_4204_ = v___x_4198_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4223_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 0, v___x_4201_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 1, v_nextMacroScope_4190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 2, v_ngen_4191_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 3, v_auxDeclNGen_4192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 4, v_traceState_4193_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 5, v___x_4202_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 6, v_messages_4194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 7, v_infoState_4195_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4223_, 8, v_snapshotTasks_4196_);
                    v___x_4204_ = v_reuseFailAlloc_4223_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4205_ = lean_st_ref_set(v___y_4186_, v___x_4204_);
                v___x_4206_ = lean_st_ref_take(v___y_4185_);
                v_mctx_4207_ = crate::leanh::lean_ctor_get(v___x_4206_, 0);
                v_zetaDeltaFVarIds_4208_ = crate::leanh::lean_ctor_get(v___x_4206_, 2);
                v_postponed_4209_ = crate::leanh::lean_ctor_get(v___x_4206_, 3);
                v_diag_4210_ = crate::leanh::lean_ctor_get(v___x_4206_, 4);
                v_isSharedCheck_4221_ = (!crate::leanh::lean_is_exclusive(v___x_4206_)) as u8;
                if v_isSharedCheck_4221_ == 0 {
                    v_unused_4222_ = crate::leanh::lean_ctor_get(v___x_4206_, 1);
                    crate::leanh::lean_dec(v_unused_4222_);
                    v___x_4212_ = v___x_4206_;
                    v_isShared_4213_ = v_isSharedCheck_4221_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4210_);
                    crate::leanh::lean_inc(v_postponed_4209_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4208_);
                    crate::leanh::lean_inc(v_mctx_4207_);
                    crate::leanh::lean_dec(v___x_4206_);
                    v___x_4212_ = crate::leanh::lean_box(0);
                    v_isShared_4213_ = v_isSharedCheck_4221_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4214_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__6);
                if v_isShared_4213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4212_, 1, v___x_4214_);
                    v___x_4216_ = v___x_4212_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4220_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_mctx_4207_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 1, v___x_4214_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4220_,
                        2,
                        v_zetaDeltaFVarIds_4208_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 3, v_postponed_4209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4220_, 4, v_diag_4210_);
                    v___x_4216_ = v_reuseFailAlloc_4220_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4217_ = lean_st_ref_set(v___y_4185_, v___x_4216_);
                v___x_4218_ = crate::leanh::lean_box(0);
                v___x_4219_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4219_, 0, v___x_4218_);
                return v___x_4219_;
            }
            6 => {
                v___x_4235_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4235_, 0, v___y_4233_);
                crate::leanh::lean_ctor_set(v___x_4235_, 1, v___y_4234_);
                v___x_4236_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_4231_, v___x_4235_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
                if crate::leanh::lean_obj_tag(v___x_4236_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4236_, 1);
                    v___y_4185_ = v___y_4170_;
                    v___y_4186_ = v___y_4172_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v_entry_4180_, 1);
                    return v___x_4236_;
                }
            }
            7 => {
                crate::leanh::lean_inc_ref(v___y_4239_);
                v___x_4240_ = l_Lean_stringToMessageData(v___y_4239_);
                v___x_4241_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4241_, 0, v___y_4238_);
                crate::leanh::lean_ctor_set(v___x_4241_, 1, v___x_4240_);
                v___x_4242_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__10);
                v___x_4243_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4243_, 0, v___x_4241_);
                crate::leanh::lean_ctor_set(v___x_4243_, 1, v___x_4242_);
                v___x_4244_ = l_Lean_MessageData_ofName(v_mod_4163_);
                v___x_4245_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4245_, 0, v___x_4243_);
                crate::leanh::lean_ctor_set(v___x_4245_, 1, v___x_4244_);
                v___x_4246_ = l_Lean_Name_isAnonymous(v_hint_4165_);
                if v___x_4246_ == 0 {
                    v___x_4247_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__12);
                    v___x_4248_ = l_Lean_MessageData_ofName(v_hint_4165_);
                    v___x_4249_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4249_, 0, v___x_4247_);
                    crate::leanh::lean_ctor_set(v___x_4249_, 1, v___x_4248_);
                    v___y_4233_ = v___x_4245_;
                    v___y_4234_ = v___x_4249_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_hint_4165_);
                    v___x_4250_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13);
                    v___y_4233_ = v___x_4245_;
                    v___y_4234_ = v___x_4250_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc_ref(v___y_4255_);
                v___x_4256_ = l_Lean_stringToMessageData(v___y_4255_);
                v___x_4257_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4257_, 0, v___x_4253_);
                crate::leanh::lean_ctor_set(v___x_4257_, 1, v___x_4256_);
                v___x_4258_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__18);
                v___x_4259_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4259_, 0, v___x_4257_);
                crate::leanh::lean_ctor_set(v___x_4259_, 1, v___x_4258_);
                if v_isMeta_4164_ == 0 {
                    v___x_4260_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__19;
                    v___y_4238_ = v___x_4259_;
                    v___y_4239_ = v___x_4260_;
                    state = 7;
                    continue;
                } else {
                    v___x_4261_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__20;
                    v___y_4238_ = v___x_4259_;
                    v___y_4239_ = v___x_4261_;
                    state = 7;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___boxed(
    mut v_mod_4266_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4267_: *mut crate::leanh::LeanObject,
    mut v_hint_4268_: *mut crate::leanh::LeanObject,
    mut v___y_4269_: *mut crate::leanh::LeanObject,
    mut v___y_4270_: *mut crate::leanh::LeanObject,
    mut v___y_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
    mut v___y_4273_: *mut crate::leanh::LeanObject,
    mut v___y_4274_: *mut crate::leanh::LeanObject,
    mut v___y_4275_: *mut crate::leanh::LeanObject,
    mut v___y_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4277_: u8 = 0;
    let mut v_res_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4277_ = (crate::leanh::lean_unbox(v_isMeta_4267_) as u8);
    v_res_4278_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_mod_4266_, v_isMeta_boxed_4277_, v_hint_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
    crate::leanh::lean_dec(v___y_4275_);
    crate::leanh::lean_dec_ref(v___y_4274_);
    crate::leanh::lean_dec(v___y_4273_);
    crate::leanh::lean_dec_ref(v___y_4272_);
    crate::leanh::lean_dec(v___y_4271_);
    crate::leanh::lean_dec_ref(v___y_4270_);
    crate::leanh::lean_dec(v___y_4269_);
    return v_res_4278_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(
    mut v_a_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: u8 = 0;
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4280_) == 0 {
                    v___x_4281_ = crate::leanh::lean_box(0);
                    return v___x_4281_;
                } else {
                    v_key_4282_ = crate::leanh::lean_ctor_get(v_x_4280_, 0);
                    v_value_4283_ = crate::leanh::lean_ctor_get(v_x_4280_, 1);
                    v_tail_4284_ = crate::leanh::lean_ctor_get(v_x_4280_, 2);
                    v___x_4285_ = lean_name_eq(v_key_4282_, v_a_4279_);
                    if v___x_4285_ == 0 {
                        v_x_4280_ = v_tail_4284_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_4283_);
                        v___x_4287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4287_, 0, v_value_4283_);
                        return v___x_4287_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg___boxed(
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_x_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4290_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_4288_, v_x_4289_);
    crate::leanh::lean_dec(v_x_4289_);
    crate::leanh::lean_dec(v_a_4288_);
    return v_res_4290_;
}
pub unsafe fn _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___closed__0()
-> u64 {
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: u64 = 0;
    v___x_4291_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4292_ = lean_uint64_of_nat(v___x_4291_);
    return v___x_4292_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(
    mut v_m_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: u64 = 0;
    let mut v___x_4299_: u64 = 0;
    let mut v___x_4300_: u64 = 0;
    let mut v_fold_4301_: u64 = 0;
    let mut v___x_4302_: u64 = 0;
    let mut v___x_4303_: u64 = 0;
    let mut v___x_4304_: u64 = 0;
    let mut v___x_4305_: usize = 0;
    let mut v___x_4306_: usize = 0;
    let mut v___x_4307_: usize = 0;
    let mut v___x_4308_: usize = 0;
    let mut v___x_4309_: usize = 0;
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: u64 = 0;
    let mut v_hash_4313_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_4295_ = crate::leanh::lean_ctor_get(v_m_4293_, 1);
                v___x_4296_ = lean_array_get_size(v_buckets_4295_);
                if crate::leanh::lean_obj_tag(v_a_4294_) == 0 {
                    v___x_4312_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___closed__0), core::ptr::addr_of_mut!(l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___closed__0_once), _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___closed__0);
                    v___y_4298_ = v___x_4312_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4313_ = crate::leanh::lean_ctor_get_uint64(
                        v_a_4294_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4298_ = v_hash_4313_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4299_ = 32u64;
                v___x_4300_ = lean_uint64_shift_right(v___y_4298_, v___x_4299_);
                v_fold_4301_ = lean_uint64_xor(v___y_4298_, v___x_4300_);
                v___x_4302_ = 16u64;
                v___x_4303_ = lean_uint64_shift_right(v_fold_4301_, v___x_4302_);
                v___x_4304_ = lean_uint64_xor(v_fold_4301_, v___x_4303_);
                v___x_4305_ = lean_uint64_to_usize(v___x_4304_);
                v___x_4306_ = lean_usize_of_nat(v___x_4296_);
                v___x_4307_ = 1usize;
                v___x_4308_ = lean_usize_sub(v___x_4306_, v___x_4307_);
                v___x_4309_ = lean_usize_land(v___x_4305_, v___x_4308_);
                v___x_4310_ = lean_array_uget_borrowed(v_buckets_4295_, v___x_4309_);
                v___x_4311_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_4294_, v___x_4310_);
                return v___x_4311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_m_4314_: *mut crate::leanh::LeanObject,
    mut v_a_4315_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4316_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v_m_4314_, v_a_4315_);
    crate::leanh::lean_dec(v_a_4315_);
    crate::leanh::lean_dec_ref(v_m_4314_);
    return v_res_4316_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(
    mut v___x_4317_: *mut crate::leanh::LeanObject,
    mut v_declName_4318_: *mut crate::leanh::LeanObject,
    mut v_as_4319_: *mut crate::leanh::LeanObject,
    mut v_sz_4320_: usize,
    mut v_i_4321_: usize,
    mut v_b_4322_: *mut crate::leanh::LeanObject,
    mut v___y_4323_: *mut crate::leanh::LeanObject,
    mut v___y_4324_: *mut crate::leanh::LeanObject,
    mut v___y_4325_: *mut crate::leanh::LeanObject,
    mut v___y_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
    mut v___y_4328_: *mut crate::leanh::LeanObject,
    mut v___y_4329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toImport_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: u8 = 0;
    let mut v___x_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: usize = 0;
    let mut v___x_4344_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4331_ = lean_usize_dec_lt(v_i_4321_, v_sz_4320_);
                if v___x_4331_ == 0 {
                    crate::leanh::lean_dec(v_declName_4318_);
                    v___x_4332_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4332_, 0, v_b_4322_);
                    return v___x_4332_;
                } else {
                    v___x_4333_ = l_Lean_Environment_header(v___x_4317_);
                    v_modules_4334_ = crate::leanh::lean_ctor_get(v___x_4333_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4334_);
                    crate::leanh::lean_dec_ref(v___x_4333_);
                    v___x_4335_ = l_Lean_instInhabitedEffectiveImport_default;
                    v_a_4336_ = lean_array_uget_borrowed(v_as_4319_, v_i_4321_);
                    v___x_4337_ = lean_array_get(v___x_4335_, v_modules_4334_, v_a_4336_);
                    crate::leanh::lean_dec_ref(v_modules_4334_);
                    v_toImport_4338_ = crate::leanh::lean_ctor_get(v___x_4337_, 0);
                    crate::leanh::lean_inc_ref(v_toImport_4338_);
                    crate::leanh::lean_dec(v___x_4337_);
                    v_module_4339_ = crate::leanh::lean_ctor_get(v_toImport_4338_, 0);
                    crate::leanh::lean_inc(v_module_4339_);
                    crate::leanh::lean_dec_ref(v_toImport_4338_);
                    v___x_4340_ = 0;
                    crate::leanh::lean_inc(v_declName_4318_);
                    v___x_4341_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_module_4339_, v___x_4340_, v_declName_4318_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
                    if crate::leanh::lean_obj_tag(v___x_4341_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4341_, 1);
                        v___x_4342_ = crate::leanh::lean_box(0);
                        v___x_4343_ = 1usize;
                        v___x_4344_ = lean_usize_add(v_i_4321_, v___x_4343_);
                        v_i_4321_ = v___x_4344_;
                        v_b_4322_ = v___x_4342_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_4318_);
                        return v___x_4341_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5___boxed(
    mut v___x_4346_: *mut crate::leanh::LeanObject,
    mut v_declName_4347_: *mut crate::leanh::LeanObject,
    mut v_as_4348_: *mut crate::leanh::LeanObject,
    mut v_sz_4349_: *mut crate::leanh::LeanObject,
    mut v_i_4350_: *mut crate::leanh::LeanObject,
    mut v_b_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
    mut v___y_4353_: *mut crate::leanh::LeanObject,
    mut v___y_4354_: *mut crate::leanh::LeanObject,
    mut v___y_4355_: *mut crate::leanh::LeanObject,
    mut v___y_4356_: *mut crate::leanh::LeanObject,
    mut v___y_4357_: *mut crate::leanh::LeanObject,
    mut v___y_4358_: *mut crate::leanh::LeanObject,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4360_: usize = 0;
    let mut v_i_boxed_4361_: usize = 0;
    let mut v_res_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4360_ = crate::leanh::lean_unbox_usize(v_sz_4349_);
    crate::leanh::lean_dec(v_sz_4349_);
    v_i_boxed_4361_ = crate::leanh::lean_unbox_usize(v_i_4350_);
    crate::leanh::lean_dec(v_i_4350_);
    v_res_4362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(v___x_4346_, v_declName_4347_, v_as_4348_, v_sz_boxed_4360_, v_i_boxed_4361_, v_b_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
    crate::leanh::lean_dec(v___y_4358_);
    crate::leanh::lean_dec_ref(v___y_4357_);
    crate::leanh::lean_dec(v___y_4356_);
    crate::leanh::lean_dec_ref(v___y_4355_);
    crate::leanh::lean_dec(v___y_4354_);
    crate::leanh::lean_dec_ref(v___y_4353_);
    crate::leanh::lean_dec(v___y_4352_);
    crate::leanh::lean_dec_ref(v_as_4348_);
    crate::leanh::lean_dec_ref(v___x_4346_);
    return v_res_4362_;
}
pub unsafe fn _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4365_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__1;
    v___x_4366_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__0;
    v___x_4367_ = l_Std_HashMap_instInhabited(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_4366_,
        v___x_4365_,
    );
    return v___x_4367_;
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(
    mut v_declName_4370_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4371_: u8,
    mut v___y_4372_: *mut crate::leanh::LeanObject,
    mut v___y_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
    mut v___y_4376_: *mut crate::leanh::LeanObject,
    mut v___y_4377_: *mut crate::leanh::LeanObject,
    mut v___y_4378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4388_: usize = 0;
    let mut v___x_4389_: usize = 0;
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4397_: u8 = 0;
    let mut v_unused_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modules_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: u8 = 0;
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4410_: u8 = 0;
    let mut v_toImport_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_module_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: u8 = 0;
    let mut v___x_4422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4380_ = lean_st_ref_get(v___y_4378_);
                v_env_4384_ = crate::leanh::lean_ctor_get(v___x_4380_, 0);
                crate::leanh::lean_inc_ref(v_env_4384_);
                crate::leanh::lean_dec(v___x_4380_);
                v___x_4399_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4384_, v_declName_4370_);
                if crate::leanh::lean_obj_tag(v___x_4399_) == 0 {
                    crate::leanh::lean_dec_ref(v_env_4384_);
                    crate::leanh::lean_dec(v_declName_4370_);
                    state = 1;
                    continue;
                } else {
                    v_val_4400_ = crate::leanh::lean_ctor_get(v___x_4399_, 0);
                    crate::leanh::lean_inc(v_val_4400_);
                    crate::leanh::lean_dec_ref_known(v___x_4399_, 1);
                    v___x_4401_ = l_Lean_Environment_header(v_env_4384_);
                    v_modules_4402_ = crate::leanh::lean_ctor_get(v___x_4401_, 3);
                    crate::leanh::lean_inc_ref(v_modules_4402_);
                    crate::leanh::lean_dec_ref(v___x_4401_);
                    v___x_4403_ = lean_array_get_size(v_modules_4402_);
                    v___x_4404_ = lean_nat_dec_lt(v_val_4400_, v___x_4403_);
                    if v___x_4404_ == 0 {
                        crate::leanh::lean_dec_ref(v_modules_4402_);
                        crate::leanh::lean_dec(v_val_4400_);
                        crate::leanh::lean_dec_ref(v_env_4384_);
                        crate::leanh::lean_dec(v_declName_4370_);
                        state = 1;
                        continue;
                    } else {
                        v___x_4405_ = lean_st_ref_get(v___y_4378_);
                        v_env_4406_ = crate::leanh::lean_ctor_get(v___x_4405_, 0);
                        crate::leanh::lean_inc_ref(v_env_4406_);
                        crate::leanh::lean_dec(v___x_4405_);
                        v___x_4407_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2_once), _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__2);
                        v___x_4408_ = lean_array_fget(v_modules_4402_, v_val_4400_);
                        crate::leanh::lean_dec(v_val_4400_);
                        crate::leanh::lean_dec_ref(v_modules_4402_);
                        if v_isMeta_4371_ == 0 {
                            crate::leanh::lean_dec_ref(v_env_4406_);
                            v___y_4410_ = v_isMeta_4371_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_declName_4370_);
                            v___x_4421_ = l_Lean_isMarkedMeta(v_env_4406_, v_declName_4370_);
                            if v___x_4421_ == 0 {
                                v___y_4410_ = v_isMeta_4371_;
                                state = 5;
                                continue;
                            } else {
                                v___x_4422_ = 0;
                                v___y_4410_ = v___x_4422_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4382_ = crate::leanh::lean_box(0);
                v___x_4383_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4383_, 0, v___x_4382_);
                return v___x_4383_;
            }
            2 => {
                v___x_4387_ = crate::leanh::lean_box(0);
                v_sz_4388_ = lean_array_size(v___y_4386_);
                v___x_4389_ = 0usize;
                v___x_4390_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__5(v_env_4384_, v_declName_4370_, v___y_4386_, v_sz_4388_, v___x_4389_, v___x_4387_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
                crate::leanh::lean_dec_ref(v___y_4386_);
                crate::leanh::lean_dec_ref(v_env_4384_);
                if crate::leanh::lean_obj_tag(v___x_4390_) == 0 {
                    v_isSharedCheck_4397_ = (!crate::leanh::lean_is_exclusive(v___x_4390_)) as u8;
                    if v_isSharedCheck_4397_ == 0 {
                        v_unused_4398_ = crate::leanh::lean_ctor_get(v___x_4390_, 0);
                        crate::leanh::lean_dec(v_unused_4398_);
                        v___x_4392_ = v___x_4390_;
                        v_isShared_4393_ = v_isSharedCheck_4397_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4390_);
                        v___x_4392_ = crate::leanh::lean_box(0);
                        v_isShared_4393_ = v_isSharedCheck_4397_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_4390_;
                }
            }
            3 => {
                if v_isShared_4393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4392_, 0, v___x_4387_);
                    v___x_4395_ = v___x_4392_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4396_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4396_, 0, v___x_4387_);
                    v___x_4395_ = v_reuseFailAlloc_4396_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4395_;
            }
            5 => {
                v_toImport_4411_ = crate::leanh::lean_ctor_get(v___x_4408_, 0);
                crate::leanh::lean_inc_ref(v_toImport_4411_);
                crate::leanh::lean_dec(v___x_4408_);
                v_module_4412_ = crate::leanh::lean_ctor_get(v_toImport_4411_, 0);
                crate::leanh::lean_inc(v_module_4412_);
                crate::leanh::lean_dec_ref(v_toImport_4411_);
                crate::leanh::lean_inc(v_declName_4370_);
                v___x_4413_ = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4(v_module_4412_, v___y_4410_, v_declName_4370_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_);
                if crate::leanh::lean_obj_tag(v___x_4413_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4413_, 1);
                    v___x_4414_ = l_Lean_indirectModUseExt;
                    v___x_4415_ = crate::leanh::lean_box(1);
                    v___x_4416_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_env_4384_);
                    v___x_4417_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                        v___x_4407_,
                        v___x_4414_,
                        v_env_4384_,
                        v___x_4415_,
                        v___x_4416_,
                    );
                    v___x_4418_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v___x_4417_, v_declName_4370_);
                    crate::leanh::lean_dec(v___x_4417_);
                    if crate::leanh::lean_obj_tag(v___x_4418_) == 0 {
                        v___x_4419_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___closed__3;
                        v___y_4386_ = v___x_4419_;
                        state = 2;
                        continue;
                    } else {
                        v_val_4420_ = crate::leanh::lean_ctor_get(v___x_4418_, 0);
                        crate::leanh::lean_inc(v_val_4420_);
                        crate::leanh::lean_dec_ref_known(v___x_4418_, 1);
                        v___y_4386_ = v_val_4420_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_4384_);
                    crate::leanh::lean_dec(v_declName_4370_);
                    return v___x_4413_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2___boxed(
    mut v_declName_4423_: *mut crate::leanh::LeanObject,
    mut v_isMeta_4424_: *mut crate::leanh::LeanObject,
    mut v___y_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
    mut v___y_4430_: *mut crate::leanh::LeanObject,
    mut v___y_4431_: *mut crate::leanh::LeanObject,
    mut v___y_4432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isMeta_boxed_4433_: u8 = 0;
    let mut v_res_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isMeta_boxed_4433_ = (crate::leanh::lean_unbox(v_isMeta_4424_) as u8);
    v_res_4434_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_declName_4423_, v_isMeta_boxed_4433_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
    crate::leanh::lean_dec(v___y_4431_);
    crate::leanh::lean_dec_ref(v___y_4430_);
    crate::leanh::lean_dec(v___y_4429_);
    crate::leanh::lean_dec_ref(v___y_4428_);
    crate::leanh::lean_dec(v___y_4427_);
    crate::leanh::lean_dec_ref(v___y_4426_);
    crate::leanh::lean_dec(v___y_4425_);
    return v_res_4434_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(
    mut v_as_x27_4435_: *mut crate::leanh::LeanObject,
    mut v_b_4436_: *mut crate::leanh::LeanObject,
    mut v___y_4437_: *mut crate::leanh::LeanObject,
    mut v___y_4438_: *mut crate::leanh::LeanObject,
    mut v___y_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4448_: u8 = 0;
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_4435_) == 0 {
                    v___x_4445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4445_, 0, v_b_4436_);
                    return v___x_4445_;
                } else {
                    v_head_4446_ = crate::leanh::lean_ctor_get(v_as_x27_4435_, 0);
                    v_tail_4447_ = crate::leanh::lean_ctor_get(v_as_x27_4435_, 1);
                    v___x_4448_ = 1;
                    crate::leanh::lean_inc(v_head_4446_);
                    v___x_4449_ = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2(v_head_4446_, v___x_4448_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
                    if crate::leanh::lean_obj_tag(v___x_4449_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4449_, 1);
                        v___x_4450_ = crate::leanh::lean_box(0);
                        v_as_x27_4435_ = v_tail_4447_;
                        v_b_4436_ = v___x_4450_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4449_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg___boxed(
    mut v_as_x27_4452_: *mut crate::leanh::LeanObject,
    mut v_b_4453_: *mut crate::leanh::LeanObject,
    mut v___y_4454_: *mut crate::leanh::LeanObject,
    mut v___y_4455_: *mut crate::leanh::LeanObject,
    mut v___y_4456_: *mut crate::leanh::LeanObject,
    mut v___y_4457_: *mut crate::leanh::LeanObject,
    mut v___y_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
    mut v___y_4460_: *mut crate::leanh::LeanObject,
    mut v___y_4461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4462_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_as_x27_4452_, v_b_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_);
    crate::leanh::lean_dec(v___y_4460_);
    crate::leanh::lean_dec_ref(v___y_4459_);
    crate::leanh::lean_dec(v___y_4458_);
    crate::leanh::lean_dec_ref(v___y_4457_);
    crate::leanh::lean_dec(v___y_4456_);
    crate::leanh::lean_dec_ref(v___y_4455_);
    crate::leanh::lean_dec(v___y_4454_);
    crate::leanh::lean_dec(v_as_x27_4452_);
    return v_res_4462_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4468_ = l_Lean_maxRecDepthErrorMessage;
    v___x_4469_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4469_, 0, v___x_4468_);
    return v___x_4469_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4470_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__3);
    v___x_4471_ = l_Lean_MessageData_ofFormat(v___x_4470_);
    return v___x_4471_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4472_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__4);
    v___x_4473_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__2;
    v___x_4474_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4474_, 0, v___x_4473_);
    crate::leanh::lean_ctor_set(v___x_4474_, 1, v___x_4472_);
    return v___x_4474_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(
    mut v_ref_4475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4477_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___closed__5);
    v___x_4478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4478_, 0, v_ref_4475_);
    crate::leanh::lean_ctor_set(v___x_4478_, 1, v___x_4477_);
    v___x_4479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4479_, 0, v___x_4478_);
    return v___x_4479_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg___boxed(
    mut v_ref_4480_: *mut crate::leanh::LeanObject,
    mut v___y_4481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4482_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_ref_4480_);
    return v_res_4482_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(
    mut v_x_4483_: *mut crate::leanh::LeanObject,
    mut v___y_4484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_4483_) == 0 {
        let mut v_a_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4485_ = crate::leanh::lean_ctor_get(v_x_4483_, 0);
        crate::leanh::lean_inc(v_a_4485_);
        v___x_4486_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4486_, 0, v_a_4485_);
        crate::leanh::lean_ctor_set(v___x_4486_, 1, v___y_4484_);
        return v___x_4486_;
    } else {
        let mut v_a_4487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_4487_ = crate::leanh::lean_ctor_get(v_x_4483_, 0);
        crate::leanh::lean_inc(v_a_4487_);
        v___x_4488_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4488_, 0, v_a_4487_);
        crate::leanh::lean_ctor_set(v___x_4488_, 1, v___y_4484_);
        return v___x_4488_;
    }
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg___boxed(
    mut v_x_4489_: *mut crate::leanh::LeanObject,
    mut v___y_4490_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4491_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_x_4489_, v___y_4490_);
    crate::leanh::lean_dec_ref(v_x_4489_);
    return v_res_4491_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(
    mut v_env_4492_: *mut crate::leanh::LeanObject,
    mut v_stx_4493_: *mut crate::leanh::LeanObject,
    mut v___y_4494_: *mut crate::leanh::LeanObject,
    mut v___y_4495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4501_: u8 = 0;
    let mut v___x_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4506_: u8 = 0;
    let mut v_unused_4507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4511_: u8 = 0;
    let mut v_snd_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4517_: u8 = 0;
    let mut v___x_4519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut v_a_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4527_: u8 = 0;
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4535_: u8 = 0;
    let mut v_isSharedCheck_4536_: u8 = 0;
    let mut v_a_4537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4541_: u8 = 0;
    let mut v___x_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4545_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4496_ = l_Lean_Elab_expandMacroImpl_x3f(
                    v_env_4492_,
                    v_stx_4493_,
                    v___y_4494_,
                    v___y_4495_,
                );
                if crate::leanh::lean_obj_tag(v___x_4496_) == 0 {
                    v_a_4497_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                    crate::leanh::lean_inc(v_a_4497_);
                    if crate::leanh::lean_obj_tag(v_a_4497_) == 0 {
                        v_a_4498_ = crate::leanh::lean_ctor_get(v___x_4496_, 1);
                        v_isSharedCheck_4506_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4496_)) as u8;
                        if v_isSharedCheck_4506_ == 0 {
                            v_unused_4507_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                            crate::leanh::lean_dec(v_unused_4507_);
                            v___x_4500_ = v___x_4496_;
                            v_isShared_4501_ = v_isSharedCheck_4506_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4498_);
                            crate::leanh::lean_dec(v___x_4496_);
                            v___x_4500_ = crate::leanh::lean_box(0);
                            v_isShared_4501_ = v_isSharedCheck_4506_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_val_4508_ = crate::leanh::lean_ctor_get(v_a_4497_, 0);
                        v_isSharedCheck_4536_ = (!crate::leanh::lean_is_exclusive(v_a_4497_)) as u8;
                        if v_isSharedCheck_4536_ == 0 {
                            v___x_4510_ = v_a_4497_;
                            v_isShared_4511_ = v_isSharedCheck_4536_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4508_);
                            crate::leanh::lean_dec(v_a_4497_);
                            v___x_4510_ = crate::leanh::lean_box(0);
                            v_isShared_4511_ = v_isSharedCheck_4536_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_4537_ = crate::leanh::lean_ctor_get(v___x_4496_, 0);
                    v_a_4538_ = crate::leanh::lean_ctor_get(v___x_4496_, 1);
                    v_isSharedCheck_4545_ = (!crate::leanh::lean_is_exclusive(v___x_4496_)) as u8;
                    if v_isSharedCheck_4545_ == 0 {
                        v___x_4540_ = v___x_4496_;
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4538_);
                        crate::leanh::lean_inc(v_a_4537_);
                        crate::leanh::lean_dec(v___x_4496_);
                        v___x_4540_ = crate::leanh::lean_box(0);
                        v_isShared_4541_ = v_isSharedCheck_4545_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4502_ = crate::leanh::lean_box(0);
                if v_isShared_4501_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4500_, 0, v___x_4502_);
                    v___x_4504_ = v___x_4500_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 1, v_a_4498_);
                    v___x_4504_ = v_reuseFailAlloc_4505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4504_;
            }
            3 => {
                v_snd_4512_ = crate::leanh::lean_ctor_get(v_val_4508_, 1);
                crate::leanh::lean_inc(v_snd_4512_);
                crate::leanh::lean_dec(v_val_4508_);
                if crate::leanh::lean_obj_tag(v_snd_4512_) == 0 {
                    crate::leanh::lean_del_object(v___x_4510_);
                    v_a_4513_ = crate::leanh::lean_ctor_get(v___x_4496_, 1);
                    crate::leanh::lean_inc(v_a_4513_);
                    crate::leanh::lean_dec_ref_known(v___x_4496_, 2);
                    v_a_4514_ = crate::leanh::lean_ctor_get(v_snd_4512_, 0);
                    v_isSharedCheck_4522_ = (!crate::leanh::lean_is_exclusive(v_snd_4512_)) as u8;
                    if v_isSharedCheck_4522_ == 0 {
                        v___x_4516_ = v_snd_4512_;
                        v_isShared_4517_ = v_isSharedCheck_4522_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4514_);
                        crate::leanh::lean_dec(v_snd_4512_);
                        v___x_4516_ = crate::leanh::lean_box(0);
                        v_isShared_4517_ = v_isSharedCheck_4522_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4523_ = crate::leanh::lean_ctor_get(v___x_4496_, 1);
                    crate::leanh::lean_inc(v_a_4523_);
                    crate::leanh::lean_dec_ref_known(v___x_4496_, 2);
                    v_a_4524_ = crate::leanh::lean_ctor_get(v_snd_4512_, 0);
                    v_isSharedCheck_4535_ = (!crate::leanh::lean_is_exclusive(v_snd_4512_)) as u8;
                    if v_isSharedCheck_4535_ == 0 {
                        v___x_4526_ = v_snd_4512_;
                        v_isShared_4527_ = v_isSharedCheck_4535_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4524_);
                        crate::leanh::lean_dec(v_snd_4512_);
                        v___x_4526_ = crate::leanh::lean_box(0);
                        v_isShared_4527_ = v_isSharedCheck_4535_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4517_ == 0 {
                    v___x_4519_ = v___x_4516_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4514_);
                    v___x_4519_ = v_reuseFailAlloc_4521_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4520_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v___x_4519_, v_a_4513_);
                crate::leanh::lean_dec_ref(v___x_4519_);
                return v___x_4520_;
            }
            6 => {
                if v_isShared_4511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4510_, 0, v_a_4524_);
                    v___x_4529_ = v___x_4510_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4534_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4524_);
                    v___x_4529_ = v_reuseFailAlloc_4534_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4527_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4526_, 0, v___x_4529_);
                    v___x_4531_ = v___x_4526_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4533_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4533_, 0, v___x_4529_);
                    v___x_4531_ = v_reuseFailAlloc_4533_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4532_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v___x_4531_, v_a_4523_);
                crate::leanh::lean_dec_ref(v___x_4531_);
                return v___x_4532_;
            }
            9 => {
                if v_isShared_4541_ == 0 {
                    v___x_4543_ = v___x_4540_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4544_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4537_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_a_4538_);
                    v___x_4543_ = v_reuseFailAlloc_4544_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4543_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed(
    mut v_env_4546_: *mut crate::leanh::LeanObject,
    mut v_stx_4547_: *mut crate::leanh::LeanObject,
    mut v___y_4548_: *mut crate::leanh::LeanObject,
    mut v___y_4549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4550_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0(
            v_env_4546_,
            v_stx_4547_,
            v___y_4548_,
            v___y_4549_,
        );
    crate::leanh::lean_dec_ref(v___y_4548_);
    return v_res_4550_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(
    mut v_env_4551_: *mut crate::leanh::LeanObject,
    mut v_options_4552_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4553_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4554_: *mut crate::leanh::LeanObject,
    mut v_n_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4558_ = l_Lean_ResolveName_resolveGlobalName(
        v_env_4551_,
        v_options_4552_,
        v_currNamespace_4553_,
        v_openDecls_4554_,
        v_n_4555_,
    );
    v___x_4559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4559_, 0, v___x_4558_);
    crate::leanh::lean_ctor_set(v___x_4559_, 1, v___y_4557_);
    return v___x_4559_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed(
    mut v_env_4560_: *mut crate::leanh::LeanObject,
    mut v_options_4561_: *mut crate::leanh::LeanObject,
    mut v_currNamespace_4562_: *mut crate::leanh::LeanObject,
    mut v_openDecls_4563_: *mut crate::leanh::LeanObject,
    mut v_n_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4567_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4(
            v_env_4560_,
            v_options_4561_,
            v_currNamespace_4562_,
            v_openDecls_4563_,
            v_n_4564_,
            v___y_4565_,
            v___y_4566_,
        );
    crate::leanh::lean_dec_ref(v___y_4565_);
    crate::leanh::lean_dec_ref(v_options_4561_);
    return v_res_4567_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(
    mut v_msg_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
    mut v___y_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4574_ = crate::leanh::lean_ctor_get(v___y_4571_, 5);
                v___x_4575_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0_spec__1(v_msg_4568_, v___y_4569_, v___y_4570_, v___y_4571_, v___y_4572_);
                v_a_4576_ = crate::leanh::lean_ctor_get(v___x_4575_, 0);
                v_isSharedCheck_4584_ = (!crate::leanh::lean_is_exclusive(v___x_4575_)) as u8;
                if v_isSharedCheck_4584_ == 0 {
                    v___x_4578_ = v___x_4575_;
                    v_isShared_4579_ = v_isSharedCheck_4584_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4576_);
                    crate::leanh::lean_dec(v___x_4575_);
                    v___x_4578_ = crate::leanh::lean_box(0);
                    v_isShared_4579_ = v_isSharedCheck_4584_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_4574_);
                v___x_4580_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4580_, 0, v_ref_4574_);
                crate::leanh::lean_ctor_set(v___x_4580_, 1, v_a_4576_);
                if v_isShared_4579_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4578_, 1);
                    crate::leanh::lean_ctor_set(v___x_4578_, 0, v___x_4580_);
                    v___x_4582_ = v___x_4578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4583_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4583_, 0, v___x_4580_);
                    v___x_4582_ = v_reuseFailAlloc_4583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg___boxed(
    mut v_msg_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
    mut v___y_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4591_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
    crate::leanh::lean_dec(v___y_4589_);
    crate::leanh::lean_dec_ref(v___y_4588_);
    crate::leanh::lean_dec(v___y_4587_);
    crate::leanh::lean_dec_ref(v___y_4586_);
    return v_res_4591_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(
    mut v_ref_4592_: *mut crate::leanh::LeanObject,
    mut v_msg_4593_: *mut crate::leanh::LeanObject,
    mut v___y_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4614_: u8 = 0;
    let mut v_cancelTk_x3f_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4616_: u8 = 0;
    let mut v_inheritedTraceOptions_4617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_4602_ = crate::leanh::lean_ctor_get(v___y_4599_, 0);
    v_fileMap_4603_ = crate::leanh::lean_ctor_get(v___y_4599_, 1);
    v_options_4604_ = crate::leanh::lean_ctor_get(v___y_4599_, 2);
    v_currRecDepth_4605_ = crate::leanh::lean_ctor_get(v___y_4599_, 3);
    v_maxRecDepth_4606_ = crate::leanh::lean_ctor_get(v___y_4599_, 4);
    v_ref_4607_ = crate::leanh::lean_ctor_get(v___y_4599_, 5);
    v_currNamespace_4608_ = crate::leanh::lean_ctor_get(v___y_4599_, 6);
    v_openDecls_4609_ = crate::leanh::lean_ctor_get(v___y_4599_, 7);
    v_initHeartbeats_4610_ = crate::leanh::lean_ctor_get(v___y_4599_, 8);
    v_maxHeartbeats_4611_ = crate::leanh::lean_ctor_get(v___y_4599_, 9);
    v_quotContext_4612_ = crate::leanh::lean_ctor_get(v___y_4599_, 10);
    v_currMacroScope_4613_ = crate::leanh::lean_ctor_get(v___y_4599_, 11);
    v_diag_4614_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4599_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_4615_ = crate::leanh::lean_ctor_get(v___y_4599_, 12);
    v_suppressElabErrors_4616_ = crate::leanh::lean_ctor_get_uint8(
        v___y_4599_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_4617_ = crate::leanh::lean_ctor_get(v___y_4599_, 13);
    v_ref_4618_ = l_Lean_replaceRef(v_ref_4592_, v_ref_4607_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4617_);
    crate::leanh::lean_inc(v_cancelTk_x3f_4615_);
    crate::leanh::lean_inc(v_currMacroScope_4613_);
    crate::leanh::lean_inc(v_quotContext_4612_);
    crate::leanh::lean_inc(v_maxHeartbeats_4611_);
    crate::leanh::lean_inc(v_initHeartbeats_4610_);
    crate::leanh::lean_inc(v_openDecls_4609_);
    crate::leanh::lean_inc(v_currNamespace_4608_);
    crate::leanh::lean_inc(v_maxRecDepth_4606_);
    crate::leanh::lean_inc(v_currRecDepth_4605_);
    crate::leanh::lean_inc_ref(v_options_4604_);
    crate::leanh::lean_inc_ref(v_fileMap_4603_);
    crate::leanh::lean_inc_ref(v_fileName_4602_);
    v___x_4619_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_4619_, 0, v_fileName_4602_);
    crate::leanh::lean_ctor_set(v___x_4619_, 1, v_fileMap_4603_);
    crate::leanh::lean_ctor_set(v___x_4619_, 2, v_options_4604_);
    crate::leanh::lean_ctor_set(v___x_4619_, 3, v_currRecDepth_4605_);
    crate::leanh::lean_ctor_set(v___x_4619_, 4, v_maxRecDepth_4606_);
    crate::leanh::lean_ctor_set(v___x_4619_, 5, v_ref_4618_);
    crate::leanh::lean_ctor_set(v___x_4619_, 6, v_currNamespace_4608_);
    crate::leanh::lean_ctor_set(v___x_4619_, 7, v_openDecls_4609_);
    crate::leanh::lean_ctor_set(v___x_4619_, 8, v_initHeartbeats_4610_);
    crate::leanh::lean_ctor_set(v___x_4619_, 9, v_maxHeartbeats_4611_);
    crate::leanh::lean_ctor_set(v___x_4619_, 10, v_quotContext_4612_);
    crate::leanh::lean_ctor_set(v___x_4619_, 11, v_currMacroScope_4613_);
    crate::leanh::lean_ctor_set(v___x_4619_, 12, v_cancelTk_x3f_4615_);
    crate::leanh::lean_ctor_set(v___x_4619_, 13, v_inheritedTraceOptions_4617_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_4619_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_4614_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_4619_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_4616_,
    );
    v___x_4620_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_4593_, v___y_4597_, v___y_4598_, v___x_4619_, v___y_4600_);
    crate::leanh::lean_dec_ref_known(v___x_4619_, 14);
    return v___x_4620_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg___boxed(
    mut v_ref_4621_: *mut crate::leanh::LeanObject,
    mut v_msg_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4631_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(
        v_ref_4621_,
        v_msg_4622_,
        v___y_4623_,
        v___y_4624_,
        v___y_4625_,
        v___y_4626_,
        v___y_4627_,
        v___y_4628_,
        v___y_4629_,
    );
    crate::leanh::lean_dec(v___y_4629_);
    crate::leanh::lean_dec_ref(v___y_4628_);
    crate::leanh::lean_dec(v___y_4627_);
    crate::leanh::lean_dec_ref(v___y_4626_);
    crate::leanh::lean_dec(v___y_4625_);
    crate::leanh::lean_dec_ref(v___y_4624_);
    crate::leanh::lean_dec(v___y_4623_);
    crate::leanh::lean_dec(v_ref_4621_);
    return v_res_4631_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(
    mut v_x_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
    mut v___y_4640_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_methods_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroScope_4666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceMsgs_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expandedMacroDecls_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4682_: u8 = 0;
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4690_: u8 = 0;
    let mut v___x_4692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4694_: u8 = 0;
    let mut v_unused_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4699_: u8 = 0;
    let mut v___x_4701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4703_: u8 = 0;
    let mut v_reuseFailAlloc_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4705_: u8 = 0;
    let mut v_unused_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4710_: u8 = 0;
    let mut v___x_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4714_: u8 = 0;
    let mut v_a_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: u8 = 0;
    let mut v___x_4720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4642_ = lean_st_ref_get(v___y_4640_);
                v_env_4643_ = crate::leanh::lean_ctor_get(v___x_4642_, 0);
                crate::leanh::lean_inc_ref_n(v_env_4643_, 4);
                crate::leanh::lean_dec(v___x_4642_);
                v_options_4644_ = crate::leanh::lean_ctor_get(v___y_4639_, 2);
                v_currRecDepth_4645_ = crate::leanh::lean_ctor_get(v___y_4639_, 3);
                v_maxRecDepth_4646_ = crate::leanh::lean_ctor_get(v___y_4639_, 4);
                v_ref_4647_ = crate::leanh::lean_ctor_get(v___y_4639_, 5);
                v_currNamespace_4648_ = crate::leanh::lean_ctor_get(v___y_4639_, 6);
                v_openDecls_4649_ = crate::leanh::lean_ctor_get(v___y_4639_, 7);
                v_quotContext_4650_ = crate::leanh::lean_ctor_get(v___y_4639_, 10);
                v_currMacroScope_4651_ = crate::leanh::lean_ctor_get(v___y_4639_, 11);
                v___x_4652_ = lean_st_ref_get(v___y_4640_);
                v_nextMacroScope_4653_ = crate::leanh::lean_ctor_get(v___x_4652_, 1);
                crate::leanh::lean_inc(v_nextMacroScope_4653_);
                crate::leanh::lean_dec(v___x_4652_);
                v___f_4654_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_4654_, 0, v_env_4643_);
                v___f_4655_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 4, 1);
                crate::leanh::lean_closure_set(v___f_4655_, 0, v_env_4643_);
                crate::leanh::lean_inc_n(v_openDecls_4649_, 2);
                crate::leanh::lean_inc_n(v_currNamespace_4648_, 3);
                v___f_4656_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__2___boxed as *mut core::ffi::c_void, 6, 3);
                crate::leanh::lean_closure_set(v___f_4656_, 0, v_env_4643_);
                crate::leanh::lean_closure_set(v___f_4656_, 1, v_currNamespace_4648_);
                crate::leanh::lean_closure_set(v___f_4656_, 2, v_openDecls_4649_);
                v___f_4657_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 1);
                crate::leanh::lean_closure_set(v___f_4657_, 0, v_currNamespace_4648_);
                crate::leanh::lean_inc_ref(v_options_4644_);
                v___f_4658_ = crate::leanh::lean_alloc_closure(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___lam__4___boxed as *mut core::ffi::c_void, 7, 4);
                crate::leanh::lean_closure_set(v___f_4658_, 0, v_env_4643_);
                crate::leanh::lean_closure_set(v___f_4658_, 1, v_options_4644_);
                crate::leanh::lean_closure_set(v___f_4658_, 2, v_currNamespace_4648_);
                crate::leanh::lean_closure_set(v___f_4658_, 3, v_openDecls_4649_);
                v_methods_4659_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v_methods_4659_, 0, v___f_4654_);
                crate::leanh::lean_ctor_set(v_methods_4659_, 1, v___f_4657_);
                crate::leanh::lean_ctor_set(v_methods_4659_, 2, v___f_4655_);
                crate::leanh::lean_ctor_set(v_methods_4659_, 3, v___f_4656_);
                crate::leanh::lean_ctor_set(v_methods_4659_, 4, v___f_4658_);
                crate::leanh::lean_inc(v_ref_4647_);
                crate::leanh::lean_inc(v_maxRecDepth_4646_);
                crate::leanh::lean_inc(v_currRecDepth_4645_);
                crate::leanh::lean_inc(v_currMacroScope_4651_);
                crate::leanh::lean_inc(v_quotContext_4650_);
                v___x_4660_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4660_, 0, v_methods_4659_);
                crate::leanh::lean_ctor_set(v___x_4660_, 1, v_quotContext_4650_);
                crate::leanh::lean_ctor_set(v___x_4660_, 2, v_currMacroScope_4651_);
                crate::leanh::lean_ctor_set(v___x_4660_, 3, v_currRecDepth_4645_);
                crate::leanh::lean_ctor_set(v___x_4660_, 4, v_maxRecDepth_4646_);
                crate::leanh::lean_ctor_set(v___x_4660_, 5, v_ref_4647_);
                v___x_4661_ = crate::leanh::lean_box(0);
                v___x_4662_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4662_, 0, v_nextMacroScope_4653_);
                crate::leanh::lean_ctor_set(v___x_4662_, 1, v___x_4661_);
                crate::leanh::lean_ctor_set(v___x_4662_, 2, v___x_4661_);
                v___x_4663_ = crate::leanh::lean_apply_2(v_x_4633_, v___x_4660_, v___x_4662_);
                if crate::leanh::lean_obj_tag(v___x_4663_) == 0 {
                    v_a_4664_ = crate::leanh::lean_ctor_get(v___x_4663_, 1);
                    crate::leanh::lean_inc(v_a_4664_);
                    v_a_4665_ = crate::leanh::lean_ctor_get(v___x_4663_, 0);
                    crate::leanh::lean_inc(v_a_4665_);
                    crate::leanh::lean_dec_ref_known(v___x_4663_, 2);
                    v_macroScope_4666_ = crate::leanh::lean_ctor_get(v_a_4664_, 0);
                    crate::leanh::lean_inc(v_macroScope_4666_);
                    v_traceMsgs_4667_ = crate::leanh::lean_ctor_get(v_a_4664_, 1);
                    crate::leanh::lean_inc(v_traceMsgs_4667_);
                    v_expandedMacroDecls_4668_ = crate::leanh::lean_ctor_get(v_a_4664_, 2);
                    crate::leanh::lean_inc(v_expandedMacroDecls_4668_);
                    crate::leanh::lean_dec(v_a_4664_);
                    v___x_4669_ = crate::leanh::lean_box(0);
                    v___x_4670_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_expandedMacroDecls_4668_, v___x_4669_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
                    crate::leanh::lean_dec(v_expandedMacroDecls_4668_);
                    if crate::leanh::lean_obj_tag(v___x_4670_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4670_, 1);
                        v___x_4671_ = lean_st_ref_take(v___y_4640_);
                        v_env_4672_ = crate::leanh::lean_ctor_get(v___x_4671_, 0);
                        v_ngen_4673_ = crate::leanh::lean_ctor_get(v___x_4671_, 2);
                        v_auxDeclNGen_4674_ = crate::leanh::lean_ctor_get(v___x_4671_, 3);
                        v_traceState_4675_ = crate::leanh::lean_ctor_get(v___x_4671_, 4);
                        v_cache_4676_ = crate::leanh::lean_ctor_get(v___x_4671_, 5);
                        v_messages_4677_ = crate::leanh::lean_ctor_get(v___x_4671_, 6);
                        v_infoState_4678_ = crate::leanh::lean_ctor_get(v___x_4671_, 7);
                        v_snapshotTasks_4679_ = crate::leanh::lean_ctor_get(v___x_4671_, 8);
                        v_isSharedCheck_4705_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4671_)) as u8;
                        if v_isSharedCheck_4705_ == 0 {
                            v_unused_4706_ = crate::leanh::lean_ctor_get(v___x_4671_, 1);
                            crate::leanh::lean_dec(v_unused_4706_);
                            v___x_4681_ = v___x_4671_;
                            v_isShared_4682_ = v_isSharedCheck_4705_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snapshotTasks_4679_);
                            crate::leanh::lean_inc(v_infoState_4678_);
                            crate::leanh::lean_inc(v_messages_4677_);
                            crate::leanh::lean_inc(v_cache_4676_);
                            crate::leanh::lean_inc(v_traceState_4675_);
                            crate::leanh::lean_inc(v_auxDeclNGen_4674_);
                            crate::leanh::lean_inc(v_ngen_4673_);
                            crate::leanh::lean_inc(v_env_4672_);
                            crate::leanh::lean_dec(v___x_4671_);
                            v___x_4681_ = crate::leanh::lean_box(0);
                            v_isShared_4682_ = v_isSharedCheck_4705_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_traceMsgs_4667_);
                        crate::leanh::lean_dec(v_macroScope_4666_);
                        crate::leanh::lean_dec(v_a_4665_);
                        v_a_4707_ = crate::leanh::lean_ctor_get(v___x_4670_, 0);
                        v_isSharedCheck_4714_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4670_)) as u8;
                        if v_isSharedCheck_4714_ == 0 {
                            v___x_4709_ = v___x_4670_;
                            v_isShared_4710_ = v_isSharedCheck_4714_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4707_);
                            crate::leanh::lean_dec(v___x_4670_);
                            v___x_4709_ = crate::leanh::lean_box(0);
                            v_isShared_4710_ = v_isSharedCheck_4714_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    v_a_4715_ = crate::leanh::lean_ctor_get(v___x_4663_, 0);
                    crate::leanh::lean_inc(v_a_4715_);
                    crate::leanh::lean_dec_ref_known(v___x_4663_, 2);
                    if crate::leanh::lean_obj_tag(v_a_4715_) == 0 {
                        v_a_4716_ = crate::leanh::lean_ctor_get(v_a_4715_, 0);
                        crate::leanh::lean_inc(v_a_4716_);
                        v_a_4717_ = crate::leanh::lean_ctor_get(v_a_4715_, 1);
                        crate::leanh::lean_inc_ref(v_a_4717_);
                        crate::leanh::lean_dec_ref_known(v_a_4715_, 2);
                        v___x_4718_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___closed__0;
                        v___x_4719_ = lean_string_dec_eq(v_a_4717_, v___x_4718_);
                        if v___x_4719_ == 0 {
                            v___x_4720_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4720_, 0, v_a_4717_);
                            v___x_4721_ = l_Lean_MessageData_ofFormat(v___x_4720_);
                            v___x_4722_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_a_4716_, v___x_4721_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
                            crate::leanh::lean_dec(v_a_4716_);
                            return v___x_4722_;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_4717_);
                            v___x_4723_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_a_4716_);
                            return v___x_4723_;
                        }
                    } else {
                        v___x_4724_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
                        return v___x_4724_;
                    }
                }
            }
            1 => {
                if v_isShared_4682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4681_, 1, v_macroScope_4666_);
                    v___x_4684_ = v___x_4681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4704_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 0, v_env_4672_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 1, v_macroScope_4666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 2, v_ngen_4673_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 3, v_auxDeclNGen_4674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 4, v_traceState_4675_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 5, v_cache_4676_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 6, v_messages_4677_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 7, v_infoState_4678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4704_, 8, v_snapshotTasks_4679_);
                    v___x_4684_ = v_reuseFailAlloc_4704_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4685_ = lean_st_ref_set(v___y_4640_, v___x_4684_);
                v___x_4686_ = l_List_reverse___redArg(v_traceMsgs_4667_);
                v___x_4687_ = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__4(v___x_4686_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
                if crate::leanh::lean_obj_tag(v___x_4687_) == 0 {
                    v_isSharedCheck_4694_ = (!crate::leanh::lean_is_exclusive(v___x_4687_)) as u8;
                    if v_isSharedCheck_4694_ == 0 {
                        v_unused_4695_ = crate::leanh::lean_ctor_get(v___x_4687_, 0);
                        crate::leanh::lean_dec(v_unused_4695_);
                        v___x_4689_ = v___x_4687_;
                        v_isShared_4690_ = v_isSharedCheck_4694_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4687_);
                        v___x_4689_ = crate::leanh::lean_box(0);
                        v_isShared_4690_ = v_isSharedCheck_4694_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4665_);
                    v_a_4696_ = crate::leanh::lean_ctor_get(v___x_4687_, 0);
                    v_isSharedCheck_4703_ = (!crate::leanh::lean_is_exclusive(v___x_4687_)) as u8;
                    if v_isSharedCheck_4703_ == 0 {
                        v___x_4698_ = v___x_4687_;
                        v_isShared_4699_ = v_isSharedCheck_4703_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4696_);
                        crate::leanh::lean_dec(v___x_4687_);
                        v___x_4698_ = crate::leanh::lean_box(0);
                        v_isShared_4699_ = v_isSharedCheck_4703_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4689_, 0, v_a_4665_);
                    v___x_4692_ = v___x_4689_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4665_);
                    v___x_4692_ = v_reuseFailAlloc_4693_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4692_;
            }
            5 => {
                if v_isShared_4699_ == 0 {
                    v___x_4701_ = v___x_4698_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4702_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
                    v___x_4701_ = v_reuseFailAlloc_4702_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4701_;
            }
            7 => {
                if v_isShared_4710_ == 0 {
                    v___x_4712_ = v___x_4709_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4713_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4713_, 0, v_a_4707_);
                    v___x_4712_ = v_reuseFailAlloc_4713_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4712_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg___boxed(
    mut v_x_4725_: *mut crate::leanh::LeanObject,
    mut v___y_4726_: *mut crate::leanh::LeanObject,
    mut v___y_4727_: *mut crate::leanh::LeanObject,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4734_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(
            v_x_4725_,
            v___y_4726_,
            v___y_4727_,
            v___y_4728_,
            v___y_4729_,
            v___y_4730_,
            v___y_4731_,
            v___y_4732_,
        );
    crate::leanh::lean_dec(v___y_4732_);
    crate::leanh::lean_dec_ref(v___y_4731_);
    crate::leanh::lean_dec(v___y_4730_);
    crate::leanh::lean_dec_ref(v___y_4729_);
    crate::leanh::lean_dec(v___y_4728_);
    crate::leanh::lean_dec_ref(v___y_4727_);
    crate::leanh::lean_dec(v___y_4726_);
    return v_res_4734_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheck___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4736_ = l_Lean_Elab_Term_Quotation_precheck___closed__0;
    v___x_4737_ = l_Lean_stringToMessageData(v___x_4736_);
    return v___x_4737_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheck___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4739_ = l_Lean_Elab_Term_Quotation_precheck___closed__2;
    v___x_4740_ = l_Lean_stringToMessageData(v___x_4739_);
    return v___x_4740_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheck___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4742_ = l_Lean_Elab_Term_Quotation_precheck___closed__4;
    v___x_4743_ = l_Lean_stringToMessageData(v___x_4742_);
    return v___x_4743_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheck___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4745_ = l_Lean_Elab_Term_Quotation_precheck___closed__6;
    v___x_4746_ = l_Lean_stringToMessageData(v___x_4745_);
    return v___x_4746_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheck___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4748_ = l_Lean_Elab_Term_Quotation_precheck___closed__8;
    v___x_4749_ = l_Lean_stringToMessageData(v___x_4748_);
    return v___x_4749_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheck___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4751_ = l_Lean_Elab_Term_Quotation_precheck___closed__10;
    v___x_4752_ = l_Lean_stringToMessageData(v___x_4751_);
    return v___x_4752_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheck(
    mut v_stx_4753_: *mut crate::leanh::LeanObject,
    mut v_a_4754_: *mut crate::leanh::LeanObject,
    mut v_a_4755_: *mut crate::leanh::LeanObject,
    mut v_a_4756_: *mut crate::leanh::LeanObject,
    mut v_a_4757_: *mut crate::leanh::LeanObject,
    mut v_a_4758_: *mut crate::leanh::LeanObject,
    mut v_a_4759_: *mut crate::leanh::LeanObject,
    mut v_a_4760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: u8 = 0;
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4782_: u8 = 0;
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4787_: u8 = 0;
    let mut v_unused_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_a_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4804_: u8 = 0;
    let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4808_: u8 = 0;
    let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4822_: u8 = 0;
    let mut v_id_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: u8 = 0;
    let mut v___y_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4851_: u8 = 0;
    let mut v_cancelTk_x3f_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4853_: u8 = 0;
    let mut v_inheritedTraceOptions_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4860_: u8 = 0;
    let mut v___x_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_unused_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: u8 = 0;
    let mut v___x_4870_: u8 = 0;
    let mut v___x_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_4874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_4882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4886_: u8 = 0;
    let mut v_cancelTk_x3f_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4888_: u8 = 0;
    let mut v_inheritedTraceOptions_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_text_x3f_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4871_ = lean_st_ref_get(v_a_4760_);
                v_env_4901_ = crate::leanh::lean_ctor_get(v___x_4871_, 0);
                crate::leanh::lean_inc_ref(v_env_4901_);
                crate::leanh::lean_dec(v___x_4871_);
                v___x_4902_ = l_Lean_Elab_deprecatedSyntaxExt;
                v_toEnvExtension_4903_ = crate::leanh::lean_ctor_get(v___x_4902_, 0);
                v_asyncMode_4904_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4903_, 2);
                v___x_4905_ = crate::leanh::lean_box(1);
                v___x_4906_ = crate::leanh::lean_box(0);
                v___x_4907_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(
                    v___x_4905_,
                    v___x_4902_,
                    v_env_4901_,
                    v_asyncMode_4904_,
                    v___x_4906_,
                );
                crate::leanh::lean_inc(v_stx_4753_);
                v___x_4908_ = l_Lean_Syntax_getKind(v_stx_4753_);
                v___x_4909_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_4907_, v___x_4908_);
                crate::leanh::lean_dec(v___x_4908_);
                crate::leanh::lean_dec(v___x_4907_);
                if crate::leanh::lean_obj_tag(v___x_4909_) == 1 {
                    v_val_4910_ = crate::leanh::lean_ctor_get(v___x_4909_, 0);
                    crate::leanh::lean_inc(v_val_4910_);
                    crate::leanh::lean_dec_ref_known(v___x_4909_, 1);
                    v_text_x3f_4911_ = crate::leanh::lean_ctor_get(v_val_4910_, 1);
                    crate::leanh::lean_inc(v_text_x3f_4911_);
                    crate::leanh::lean_dec(v_val_4910_);
                    if crate::leanh::lean_obj_tag(v_text_x3f_4911_) == 0 {
                        v___x_4912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13), core::ptr::addr_of_mut!(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13_once), _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4___closed__13);
                        v___y_4873_ = v___x_4912_;
                        state = 11;
                        continue;
                    } else {
                        v_val_4913_ = crate::leanh::lean_ctor_get(v_text_x3f_4911_, 0);
                        crate::leanh::lean_inc(v_val_4913_);
                        crate::leanh::lean_dec_ref_known(v_text_x3f_4911_, 1);
                        v___x_4914_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_Quotation_precheck___closed__11
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Term_Quotation_precheck___closed__11_once
                            ),
                            _init_l_Lean_Elab_Term_Quotation_precheck___closed__11,
                        );
                        v___x_4915_ = l_Lean_stringToMessageData(v_val_4913_);
                        v___x_4916_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4916_, 0, v___x_4914_);
                        crate::leanh::lean_ctor_set(v___x_4916_, 1, v___x_4915_);
                        v___y_4873_ = v___x_4916_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4909_);
                    v___y_4826_ = v_a_4754_;
                    v___y_4827_ = v_a_4755_;
                    v___y_4828_ = v_a_4756_;
                    v___y_4829_ = v_a_4757_;
                    v___y_4830_ = v_a_4758_;
                    v___y_4831_ = v_a_4759_;
                    v___y_4832_ = v_a_4760_;
                    state = 8;
                    continue;
                }
            }
            1 => {
                v___x_4763_ = crate::leanh::lean_box(0);
                v___x_4764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4764_, 0, v___x_4763_);
                return v___x_4764_;
            }
            2 => {
                crate::leanh::lean_inc(v_stx_4753_);
                v___x_4773_ = l_Lean_Syntax_isAnyAntiquot(v_stx_4753_);
                if v___x_4773_ == 0 {
                    crate::leanh::lean_inc(v_stx_4753_);
                    v___x_4774_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent(v_stx_4753_);
                    if v___x_4774_ == 0 {
                        crate::leanh::lean_dec(v_stx_4753_);
                        state = 1;
                        continue;
                    } else {
                        if v___x_4773_ == 0 {
                            crate::leanh::lean_inc(v_stx_4753_);
                            v___x_4775_ = crate::leanh::lean_alloc_closure(
                                l_Lean_Macro_expandMacro_x3f___boxed as *mut core::ffi::c_void,
                                3,
                                1,
                            );
                            crate::leanh::lean_closure_set(v___x_4775_, 0, v_stx_4753_);
                            v___x_4776_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(v___x_4775_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
                            if crate::leanh::lean_obj_tag(v___x_4776_) == 0 {
                                v_a_4777_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                                crate::leanh::lean_inc(v_a_4777_);
                                crate::leanh::lean_dec_ref_known(v___x_4776_, 1);
                                if crate::leanh::lean_obj_tag(v_a_4777_) == 1 {
                                    crate::leanh::lean_dec(v_stx_4753_);
                                    v_val_4778_ = crate::leanh::lean_ctor_get(v_a_4777_, 0);
                                    crate::leanh::lean_inc(v_val_4778_);
                                    crate::leanh::lean_dec_ref_known(v_a_4777_, 1);
                                    v___x_4779_ = l_Lean_Elab_Term_Quotation_precheck(
                                        v_val_4778_,
                                        v___y_4766_,
                                        v___y_4767_,
                                        v___y_4768_,
                                        v___y_4769_,
                                        v___y_4770_,
                                        v___y_4771_,
                                        v___y_4772_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4779_) == 0 {
                                        v_isSharedCheck_4787_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4779_)) as u8;
                                        if v_isSharedCheck_4787_ == 0 {
                                            v_unused_4788_ =
                                                crate::leanh::lean_ctor_get(v___x_4779_, 0);
                                            crate::leanh::lean_dec(v_unused_4788_);
                                            v___x_4781_ = v___x_4779_;
                                            v_isShared_4782_ = v_isSharedCheck_4787_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_4779_);
                                            v___x_4781_ = crate::leanh::lean_box(0);
                                            v_isShared_4782_ = v_isSharedCheck_4787_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        return v___x_4779_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4777_);
                                    v___x_4789_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Elab_Term_Quotation_precheck___closed__1
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Elab_Term_Quotation_precheck___closed__1_once
                                        ),
                                        _init_l_Lean_Elab_Term_Quotation_precheck___closed__1,
                                    );
                                    crate::leanh::lean_inc_n(v_stx_4753_, 2);
                                    v___x_4790_ = l_Lean_Syntax_getKind(v_stx_4753_);
                                    v___x_4791_ = l_Lean_MessageData_ofName(v___x_4790_);
                                    v___x_4792_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4792_, 0, v___x_4789_);
                                    crate::leanh::lean_ctor_set(v___x_4792_, 1, v___x_4791_);
                                    v___x_4793_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Elab_Term_Quotation_precheck___closed__3
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Elab_Term_Quotation_precheck___closed__3_once
                                        ),
                                        _init_l_Lean_Elab_Term_Quotation_precheck___closed__3,
                                    );
                                    v___x_4794_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4794_, 0, v___x_4792_);
                                    crate::leanh::lean_ctor_set(v___x_4794_, 1, v___x_4793_);
                                    v___x_4795_ = l_Lean_MessageData_ofSyntax(v_stx_4753_);
                                    v___x_4796_ = l_Lean_indentD(v___x_4795_);
                                    v___x_4797_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4797_, 0, v___x_4794_);
                                    crate::leanh::lean_ctor_set(v___x_4797_, 1, v___x_4796_);
                                    v___x_4798_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Elab_Term_Quotation_precheck___closed__5
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Elab_Term_Quotation_precheck___closed__5_once
                                        ),
                                        _init_l_Lean_Elab_Term_Quotation_precheck___closed__5,
                                    );
                                    v___x_4799_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4799_, 0, v___x_4797_);
                                    crate::leanh::lean_ctor_set(v___x_4799_, 1, v___x_4798_);
                                    v___x_4800_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_4753_, v___x_4799_, v___y_4766_, v___y_4767_, v___y_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_);
                                    crate::leanh::lean_dec(v_stx_4753_);
                                    return v___x_4800_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_stx_4753_);
                                v_a_4801_ = crate::leanh::lean_ctor_get(v___x_4776_, 0);
                                v_isSharedCheck_4808_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4776_)) as u8;
                                if v_isSharedCheck_4808_ == 0 {
                                    v___x_4803_ = v___x_4776_;
                                    v_isShared_4804_ = v_isSharedCheck_4808_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4801_);
                                    crate::leanh::lean_dec(v___x_4776_);
                                    v___x_4803_ = crate::leanh::lean_box(0);
                                    v_isShared_4804_ = v_isSharedCheck_4808_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_stx_4753_);
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_4753_);
                    v___x_4809_ = crate::leanh::lean_box(0);
                    v___x_4810_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4810_, 0, v___x_4809_);
                    return v___x_4810_;
                }
            }
            3 => {
                v___x_4783_ = crate::leanh::lean_box(0);
                if v_isShared_4782_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4781_, 0, v___x_4783_);
                    v___x_4785_ = v___x_4781_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4786_, 0, v___x_4783_);
                    v___x_4785_ = v_reuseFailAlloc_4786_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4785_;
            }
            5 => {
                if v_isShared_4804_ == 0 {
                    v___x_4806_ = v___x_4803_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4807_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4801_);
                    v___x_4806_ = v_reuseFailAlloc_4807_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4806_;
            }
            7 => {
                if v___y_4822_ == 0 {
                    if crate::leanh::lean_obj_tag(v___y_4818_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_4818_, 2);
                        crate::leanh::lean_dec(v_stx_4753_);
                        return v___y_4820_;
                    } else {
                        v_id_4823_ = crate::leanh::lean_ctor_get(v___y_4818_, 0);
                        crate::leanh::lean_inc(v_id_4823_);
                        crate::leanh::lean_dec_ref_known(v___y_4818_, 2);
                        v___x_4824_ =
                            l_Lean_instBEqInternalExceptionId_beq(v___y_4819_, v_id_4823_);
                        crate::leanh::lean_dec(v_id_4823_);
                        if v___x_4824_ == 0 {
                            crate::leanh::lean_dec(v_stx_4753_);
                            return v___y_4820_;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4820_);
                            v___y_4766_ = v___y_4816_;
                            v___y_4767_ = v___y_4814_;
                            v___y_4768_ = v___y_4812_;
                            v___y_4769_ = v___y_4821_;
                            v___y_4770_ = v___y_4815_;
                            v___y_4771_ = v___y_4813_;
                            v___y_4772_ = v___y_4817_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4818_);
                    crate::leanh::lean_dec(v_stx_4753_);
                    return v___y_4820_;
                }
            }
            8 => {
                v___x_4833_ = lean_st_ref_get(v___y_4832_);
                v_env_4834_ = crate::leanh::lean_ctor_get(v___x_4833_, 0);
                crate::leanh::lean_inc_ref(v_env_4834_);
                crate::leanh::lean_dec(v___x_4833_);
                v___x_4835_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
                crate::leanh::lean_inc(v_stx_4753_);
                v___x_4836_ = l_Lean_Syntax_getKind(v_stx_4753_);
                v___x_4837_ = l_Lean_KeyedDeclsAttribute_getValues___redArg(
                    v___x_4835_,
                    v_env_4834_,
                    v___x_4836_,
                );
                crate::leanh::lean_dec(v___x_4836_);
                if crate::leanh::lean_obj_tag(v___x_4837_) == 1 {
                    v_head_4838_ = crate::leanh::lean_ctor_get(v___x_4837_, 0);
                    crate::leanh::lean_inc(v_head_4838_);
                    crate::leanh::lean_dec_ref_known(v___x_4837_, 2);
                    v_fileName_4839_ = crate::leanh::lean_ctor_get(v___y_4831_, 0);
                    v_fileMap_4840_ = crate::leanh::lean_ctor_get(v___y_4831_, 1);
                    v_options_4841_ = crate::leanh::lean_ctor_get(v___y_4831_, 2);
                    v_currRecDepth_4842_ = crate::leanh::lean_ctor_get(v___y_4831_, 3);
                    v_maxRecDepth_4843_ = crate::leanh::lean_ctor_get(v___y_4831_, 4);
                    v_ref_4844_ = crate::leanh::lean_ctor_get(v___y_4831_, 5);
                    v_currNamespace_4845_ = crate::leanh::lean_ctor_get(v___y_4831_, 6);
                    v_openDecls_4846_ = crate::leanh::lean_ctor_get(v___y_4831_, 7);
                    v_initHeartbeats_4847_ = crate::leanh::lean_ctor_get(v___y_4831_, 8);
                    v_maxHeartbeats_4848_ = crate::leanh::lean_ctor_get(v___y_4831_, 9);
                    v_quotContext_4849_ = crate::leanh::lean_ctor_get(v___y_4831_, 10);
                    v_currMacroScope_4850_ = crate::leanh::lean_ctor_get(v___y_4831_, 11);
                    v_diag_4851_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4831_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_4852_ = crate::leanh::lean_ctor_get(v___y_4831_, 12);
                    v_suppressElabErrors_4853_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4831_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_4854_ = crate::leanh::lean_ctor_get(v___y_4831_, 13);
                    v_ref_4855_ = l_Lean_replaceRef(v_stx_4753_, v_ref_4844_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4854_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_4852_);
                    crate::leanh::lean_inc(v_currMacroScope_4850_);
                    crate::leanh::lean_inc(v_quotContext_4849_);
                    crate::leanh::lean_inc(v_maxHeartbeats_4848_);
                    crate::leanh::lean_inc(v_initHeartbeats_4847_);
                    crate::leanh::lean_inc(v_openDecls_4846_);
                    crate::leanh::lean_inc(v_currNamespace_4845_);
                    crate::leanh::lean_inc(v_maxRecDepth_4843_);
                    crate::leanh::lean_inc(v_currRecDepth_4842_);
                    crate::leanh::lean_inc_ref(v_options_4841_);
                    crate::leanh::lean_inc_ref(v_fileMap_4840_);
                    crate::leanh::lean_inc_ref(v_fileName_4839_);
                    v___x_4856_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_4856_, 0, v_fileName_4839_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 1, v_fileMap_4840_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 2, v_options_4841_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 3, v_currRecDepth_4842_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 4, v_maxRecDepth_4843_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 5, v_ref_4855_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 6, v_currNamespace_4845_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 7, v_openDecls_4846_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 8, v_initHeartbeats_4847_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 9, v_maxHeartbeats_4848_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 10, v_quotContext_4849_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 11, v_currMacroScope_4850_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 12, v_cancelTk_x3f_4852_);
                    crate::leanh::lean_ctor_set(v___x_4856_, 13, v_inheritedTraceOptions_4854_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4856_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_4851_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_4856_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_4853_,
                    );
                    crate::leanh::lean_inc(v___y_4832_);
                    crate::leanh::lean_inc(v___y_4830_);
                    crate::leanh::lean_inc_ref(v___y_4829_);
                    crate::leanh::lean_inc(v___y_4828_);
                    crate::leanh::lean_inc_ref(v___y_4827_);
                    crate::leanh::lean_inc(v___y_4826_);
                    crate::leanh::lean_inc(v_stx_4753_);
                    v___x_4857_ = crate::leanh::lean_apply_9(
                        v_head_4838_,
                        v_stx_4753_,
                        v___y_4826_,
                        v___y_4827_,
                        v___y_4828_,
                        v___y_4829_,
                        v___y_4830_,
                        v___x_4856_,
                        v___y_4832_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_4857_) == 0 {
                        crate::leanh::lean_dec(v_stx_4753_);
                        v_isSharedCheck_4865_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4857_)) as u8;
                        if v_isSharedCheck_4865_ == 0 {
                            v_unused_4866_ = crate::leanh::lean_ctor_get(v___x_4857_, 0);
                            crate::leanh::lean_dec(v_unused_4866_);
                            v___x_4859_ = v___x_4857_;
                            v_isShared_4860_ = v_isSharedCheck_4865_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4857_);
                            v___x_4859_ = crate::leanh::lean_box(0);
                            v_isShared_4860_ = v_isSharedCheck_4865_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_4867_ = crate::leanh::lean_ctor_get(v___x_4857_, 0);
                        crate::leanh::lean_inc(v_a_4867_);
                        v___x_4868_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
                        v___x_4869_ = l_Lean_Exception_isInterrupt(v_a_4867_);
                        if v___x_4869_ == 0 {
                            crate::leanh::lean_inc(v_a_4867_);
                            v___x_4870_ = l_Lean_Exception_isRuntime(v_a_4867_);
                            v___y_4812_ = v___y_4828_;
                            v___y_4813_ = v___y_4831_;
                            v___y_4814_ = v___y_4827_;
                            v___y_4815_ = v___y_4830_;
                            v___y_4816_ = v___y_4826_;
                            v___y_4817_ = v___y_4832_;
                            v___y_4818_ = v_a_4867_;
                            v___y_4819_ = v___x_4868_;
                            v___y_4820_ = v___x_4857_;
                            v___y_4821_ = v___y_4829_;
                            v___y_4822_ = v___x_4870_;
                            state = 7;
                            continue;
                        } else {
                            v___y_4812_ = v___y_4828_;
                            v___y_4813_ = v___y_4831_;
                            v___y_4814_ = v___y_4827_;
                            v___y_4815_ = v___y_4830_;
                            v___y_4816_ = v___y_4826_;
                            v___y_4817_ = v___y_4832_;
                            v___y_4818_ = v_a_4867_;
                            v___y_4819_ = v___x_4868_;
                            v___y_4820_ = v___x_4857_;
                            v___y_4821_ = v___y_4829_;
                            v___y_4822_ = v___x_4869_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4837_);
                    v___y_4766_ = v___y_4826_;
                    v___y_4767_ = v___y_4827_;
                    v___y_4768_ = v___y_4828_;
                    v___y_4769_ = v___y_4829_;
                    v___y_4770_ = v___y_4830_;
                    v___y_4771_ = v___y_4831_;
                    v___y_4772_ = v___y_4832_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v___x_4861_ = crate::leanh::lean_box(0);
                if v_isShared_4860_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4859_, 0, v___x_4861_);
                    v___x_4863_ = v___x_4859_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4861_);
                    v___x_4863_ = v_reuseFailAlloc_4864_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4863_;
            }
            11 => {
                v_fileName_4874_ = crate::leanh::lean_ctor_get(v_a_4759_, 0);
                v_fileMap_4875_ = crate::leanh::lean_ctor_get(v_a_4759_, 1);
                v_options_4876_ = crate::leanh::lean_ctor_get(v_a_4759_, 2);
                v_currRecDepth_4877_ = crate::leanh::lean_ctor_get(v_a_4759_, 3);
                v_maxRecDepth_4878_ = crate::leanh::lean_ctor_get(v_a_4759_, 4);
                v_ref_4879_ = crate::leanh::lean_ctor_get(v_a_4759_, 5);
                v_currNamespace_4880_ = crate::leanh::lean_ctor_get(v_a_4759_, 6);
                v_openDecls_4881_ = crate::leanh::lean_ctor_get(v_a_4759_, 7);
                v_initHeartbeats_4882_ = crate::leanh::lean_ctor_get(v_a_4759_, 8);
                v_maxHeartbeats_4883_ = crate::leanh::lean_ctor_get(v_a_4759_, 9);
                v_quotContext_4884_ = crate::leanh::lean_ctor_get(v_a_4759_, 10);
                v_currMacroScope_4885_ = crate::leanh::lean_ctor_get(v_a_4759_, 11);
                v_diag_4886_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4759_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_4887_ = crate::leanh::lean_ctor_get(v_a_4759_, 12);
                v_suppressElabErrors_4888_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4759_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_4889_ = crate::leanh::lean_ctor_get(v_a_4759_, 13);
                v___x_4890_ = l_Lean_Linter_linter_deprecated_syntax;
                v___x_4891_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheck___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheck___closed__7_once),
                    _init_l_Lean_Elab_Term_Quotation_precheck___closed__7,
                );
                crate::leanh::lean_inc(v_stx_4753_);
                v___x_4892_ = l_Lean_Syntax_getKind(v_stx_4753_);
                v___x_4893_ = l_Lean_MessageData_ofName(v___x_4892_);
                v___x_4894_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4894_, 0, v___x_4891_);
                crate::leanh::lean_ctor_set(v___x_4894_, 1, v___x_4893_);
                v___x_4895_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheck___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheck___closed__9_once),
                    _init_l_Lean_Elab_Term_Quotation_precheck___closed__9,
                );
                v___x_4896_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4896_, 0, v___x_4894_);
                crate::leanh::lean_ctor_set(v___x_4896_, 1, v___x_4895_);
                v___x_4897_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4897_, 0, v___x_4896_);
                crate::leanh::lean_ctor_set(v___x_4897_, 1, v___y_4873_);
                v_ref_4898_ = l_Lean_replaceRef(v_stx_4753_, v_ref_4879_);
                crate::leanh::lean_inc_ref(v_inheritedTraceOptions_4889_);
                crate::leanh::lean_inc(v_cancelTk_x3f_4887_);
                crate::leanh::lean_inc(v_currMacroScope_4885_);
                crate::leanh::lean_inc(v_quotContext_4884_);
                crate::leanh::lean_inc(v_maxHeartbeats_4883_);
                crate::leanh::lean_inc(v_initHeartbeats_4882_);
                crate::leanh::lean_inc(v_openDecls_4881_);
                crate::leanh::lean_inc(v_currNamespace_4880_);
                crate::leanh::lean_inc(v_maxRecDepth_4878_);
                crate::leanh::lean_inc(v_currRecDepth_4877_);
                crate::leanh::lean_inc_ref(v_options_4876_);
                crate::leanh::lean_inc_ref(v_fileMap_4875_);
                crate::leanh::lean_inc_ref(v_fileName_4874_);
                v___x_4899_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                crate::leanh::lean_ctor_set(v___x_4899_, 0, v_fileName_4874_);
                crate::leanh::lean_ctor_set(v___x_4899_, 1, v_fileMap_4875_);
                crate::leanh::lean_ctor_set(v___x_4899_, 2, v_options_4876_);
                crate::leanh::lean_ctor_set(v___x_4899_, 3, v_currRecDepth_4877_);
                crate::leanh::lean_ctor_set(v___x_4899_, 4, v_maxRecDepth_4878_);
                crate::leanh::lean_ctor_set(v___x_4899_, 5, v_ref_4898_);
                crate::leanh::lean_ctor_set(v___x_4899_, 6, v_currNamespace_4880_);
                crate::leanh::lean_ctor_set(v___x_4899_, 7, v_openDecls_4881_);
                crate::leanh::lean_ctor_set(v___x_4899_, 8, v_initHeartbeats_4882_);
                crate::leanh::lean_ctor_set(v___x_4899_, 9, v_maxHeartbeats_4883_);
                crate::leanh::lean_ctor_set(v___x_4899_, 10, v_quotContext_4884_);
                crate::leanh::lean_ctor_set(v___x_4899_, 11, v_currMacroScope_4885_);
                crate::leanh::lean_ctor_set(v___x_4899_, 12, v_cancelTk_x3f_4887_);
                crate::leanh::lean_ctor_set(v___x_4899_, 13, v_inheritedTraceOptions_4889_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4899_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                    v_diag_4886_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4899_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_4888_,
                );
                v___x_4900_ =
                    l_Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2(
                        v___x_4890_,
                        v_stx_4753_,
                        v___x_4897_,
                        v_a_4754_,
                        v_a_4755_,
                        v_a_4756_,
                        v_a_4757_,
                        v_a_4758_,
                        v___x_4899_,
                        v_a_4760_,
                    );
                crate::leanh::lean_dec_ref_known(v___x_4899_, 14);
                if crate::leanh::lean_obj_tag(v___x_4900_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4900_, 1);
                    v___y_4826_ = v_a_4754_;
                    v___y_4827_ = v_a_4755_;
                    v___y_4828_ = v_a_4756_;
                    v___y_4829_ = v_a_4757_;
                    v___y_4830_ = v_a_4758_;
                    v___y_4831_ = v_a_4759_;
                    v___y_4832_ = v_a_4760_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_stx_4753_);
                    return v___x_4900_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheck___boxed(
    mut v_stx_4917_: *mut crate::leanh::LeanObject,
    mut v_a_4918_: *mut crate::leanh::LeanObject,
    mut v_a_4919_: *mut crate::leanh::LeanObject,
    mut v_a_4920_: *mut crate::leanh::LeanObject,
    mut v_a_4921_: *mut crate::leanh::LeanObject,
    mut v_a_4922_: *mut crate::leanh::LeanObject,
    mut v_a_4923_: *mut crate::leanh::LeanObject,
    mut v_a_4924_: *mut crate::leanh::LeanObject,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4926_ = l_Lean_Elab_Term_Quotation_precheck(
        v_stx_4917_,
        v_a_4918_,
        v_a_4919_,
        v_a_4920_,
        v_a_4921_,
        v_a_4922_,
        v_a_4923_,
        v_a_4924_,
    );
    crate::leanh::lean_dec(v_a_4924_);
    crate::leanh::lean_dec_ref(v_a_4923_);
    crate::leanh::lean_dec(v_a_4922_);
    crate::leanh::lean_dec_ref(v_a_4921_);
    crate::leanh::lean_dec(v_a_4920_);
    crate::leanh::lean_dec_ref(v_a_4919_);
    crate::leanh::lean_dec(v_a_4918_);
    return v_res_4926_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(
    mut v_00_u03b1_4927_: *mut crate::leanh::LeanObject,
    mut v_x_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4931_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___redArg(v_x_4928_, v___y_4930_);
    return v___x_4931_;
}
pub unsafe fn l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1___boxed(
    mut v_00_u03b1_4932_: *mut crate::leanh::LeanObject,
    mut v_x_4933_: *mut crate::leanh::LeanObject,
    mut v___y_4934_: *mut crate::leanh::LeanObject,
    mut v___y_4935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4936_ = l_liftExcept___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__1(v_00_u03b1_4932_, v_x_4933_, v___y_4934_, v___y_4935_);
    crate::leanh::lean_dec_ref(v___y_4934_);
    crate::leanh::lean_dec_ref(v_x_4933_);
    return v_res_4936_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(
    mut v_00_u03b1_4937_: *mut crate::leanh::LeanObject,
    mut v_ref_4938_: *mut crate::leanh::LeanObject,
    mut v___y_4939_: *mut crate::leanh::LeanObject,
    mut v___y_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
    mut v___y_4945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4947_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___redArg(v_ref_4938_);
    return v___x_4947_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5___boxed(
    mut v_00_u03b1_4948_: *mut crate::leanh::LeanObject,
    mut v_ref_4949_: *mut crate::leanh::LeanObject,
    mut v___y_4950_: *mut crate::leanh::LeanObject,
    mut v___y_4951_: *mut crate::leanh::LeanObject,
    mut v___y_4952_: *mut crate::leanh::LeanObject,
    mut v___y_4953_: *mut crate::leanh::LeanObject,
    mut v___y_4954_: *mut crate::leanh::LeanObject,
    mut v___y_4955_: *mut crate::leanh::LeanObject,
    mut v___y_4956_: *mut crate::leanh::LeanObject,
    mut v___y_4957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4958_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__5(v_00_u03b1_4948_, v_ref_4949_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_, v___y_4954_, v___y_4955_, v___y_4956_);
    crate::leanh::lean_dec(v___y_4956_);
    crate::leanh::lean_dec_ref(v___y_4955_);
    crate::leanh::lean_dec(v___y_4954_);
    crate::leanh::lean_dec_ref(v___y_4953_);
    crate::leanh::lean_dec(v___y_4952_);
    crate::leanh::lean_dec_ref(v___y_4951_);
    crate::leanh::lean_dec(v___y_4950_);
    return v_res_4958_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(
    mut v_00_u03b1_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
    mut v___y_4963_: *mut crate::leanh::LeanObject,
    mut v___y_4964_: *mut crate::leanh::LeanObject,
    mut v___y_4965_: *mut crate::leanh::LeanObject,
    mut v___y_4966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4968_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
    return v___x_4968_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___boxed(
    mut v_00_u03b1_4969_: *mut crate::leanh::LeanObject,
    mut v___y_4970_: *mut crate::leanh::LeanObject,
    mut v___y_4971_: *mut crate::leanh::LeanObject,
    mut v___y_4972_: *mut crate::leanh::LeanObject,
    mut v___y_4973_: *mut crate::leanh::LeanObject,
    mut v___y_4974_: *mut crate::leanh::LeanObject,
    mut v___y_4975_: *mut crate::leanh::LeanObject,
    mut v___y_4976_: *mut crate::leanh::LeanObject,
    mut v___y_4977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4978_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6(v_00_u03b1_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
    crate::leanh::lean_dec(v___y_4976_);
    crate::leanh::lean_dec_ref(v___y_4975_);
    crate::leanh::lean_dec(v___y_4974_);
    crate::leanh::lean_dec_ref(v___y_4973_);
    crate::leanh::lean_dec(v___y_4972_);
    crate::leanh::lean_dec_ref(v___y_4971_);
    crate::leanh::lean_dec(v___y_4970_);
    return v_res_4978_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(
    mut v_00_u03b1_4979_: *mut crate::leanh::LeanObject,
    mut v_x_4980_: *mut crate::leanh::LeanObject,
    mut v___y_4981_: *mut crate::leanh::LeanObject,
    mut v___y_4982_: *mut crate::leanh::LeanObject,
    mut v___y_4983_: *mut crate::leanh::LeanObject,
    mut v___y_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4989_ =
        l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___redArg(
            v_x_4980_,
            v___y_4981_,
            v___y_4982_,
            v___y_4983_,
            v___y_4984_,
            v___y_4985_,
            v___y_4986_,
            v___y_4987_,
        );
    return v___x_4989_;
}
pub unsafe fn l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0___boxed(
    mut v_00_u03b1_4990_: *mut crate::leanh::LeanObject,
    mut v_x_4991_: *mut crate::leanh::LeanObject,
    mut v___y_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
    mut v___y_4998_: *mut crate::leanh::LeanObject,
    mut v___y_4999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5000_ = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0(
        v_00_u03b1_4990_,
        v_x_4991_,
        v___y_4992_,
        v___y_4993_,
        v___y_4994_,
        v___y_4995_,
        v___y_4996_,
        v___y_4997_,
        v___y_4998_,
    );
    crate::leanh::lean_dec(v___y_4998_);
    crate::leanh::lean_dec_ref(v___y_4997_);
    crate::leanh::lean_dec(v___y_4996_);
    crate::leanh::lean_dec_ref(v___y_4995_);
    crate::leanh::lean_dec(v___y_4994_);
    crate::leanh::lean_dec_ref(v___y_4993_);
    crate::leanh::lean_dec(v___y_4992_);
    return v_res_5000_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(
    mut v_00_u03b1_5001_: *mut crate::leanh::LeanObject,
    mut v_ref_5002_: *mut crate::leanh::LeanObject,
    mut v_msg_5003_: *mut crate::leanh::LeanObject,
    mut v___y_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5012_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(
        v_ref_5002_,
        v_msg_5003_,
        v___y_5004_,
        v___y_5005_,
        v___y_5006_,
        v___y_5007_,
        v___y_5008_,
        v___y_5009_,
        v___y_5010_,
    );
    return v___x_5012_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___boxed(
    mut v_00_u03b1_5013_: *mut crate::leanh::LeanObject,
    mut v_ref_5014_: *mut crate::leanh::LeanObject,
    mut v_msg_5015_: *mut crate::leanh::LeanObject,
    mut v___y_5016_: *mut crate::leanh::LeanObject,
    mut v___y_5017_: *mut crate::leanh::LeanObject,
    mut v___y_5018_: *mut crate::leanh::LeanObject,
    mut v___y_5019_: *mut crate::leanh::LeanObject,
    mut v___y_5020_: *mut crate::leanh::LeanObject,
    mut v___y_5021_: *mut crate::leanh::LeanObject,
    mut v___y_5022_: *mut crate::leanh::LeanObject,
    mut v___y_5023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5024_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1(
        v_00_u03b1_5013_,
        v_ref_5014_,
        v_msg_5015_,
        v___y_5016_,
        v___y_5017_,
        v___y_5018_,
        v___y_5019_,
        v___y_5020_,
        v___y_5021_,
        v___y_5022_,
    );
    crate::leanh::lean_dec(v___y_5022_);
    crate::leanh::lean_dec_ref(v___y_5021_);
    crate::leanh::lean_dec(v___y_5020_);
    crate::leanh::lean_dec_ref(v___y_5019_);
    crate::leanh::lean_dec(v___y_5018_);
    crate::leanh::lean_dec_ref(v___y_5017_);
    crate::leanh::lean_dec(v___y_5016_);
    crate::leanh::lean_dec(v_ref_5014_);
    return v_res_5024_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(
    mut v_cls_5025_: *mut crate::leanh::LeanObject,
    mut v_msg_5026_: *mut crate::leanh::LeanObject,
    mut v___y_5027_: *mut crate::leanh::LeanObject,
    mut v___y_5028_: *mut crate::leanh::LeanObject,
    mut v___y_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
    mut v___y_5031_: *mut crate::leanh::LeanObject,
    mut v___y_5032_: *mut crate::leanh::LeanObject,
    mut v___y_5033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5035_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg(v_cls_5025_, v_msg_5026_, v___y_5030_, v___y_5031_, v___y_5032_, v___y_5033_);
    return v___x_5035_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___boxed(
    mut v_cls_5036_: *mut crate::leanh::LeanObject,
    mut v_msg_5037_: *mut crate::leanh::LeanObject,
    mut v___y_5038_: *mut crate::leanh::LeanObject,
    mut v___y_5039_: *mut crate::leanh::LeanObject,
    mut v___y_5040_: *mut crate::leanh::LeanObject,
    mut v___y_5041_: *mut crate::leanh::LeanObject,
    mut v___y_5042_: *mut crate::leanh::LeanObject,
    mut v___y_5043_: *mut crate::leanh::LeanObject,
    mut v___y_5044_: *mut crate::leanh::LeanObject,
    mut v___y_5045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5046_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0(v_cls_5036_, v_msg_5037_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_, v___y_5042_, v___y_5043_, v___y_5044_);
    crate::leanh::lean_dec(v___y_5044_);
    crate::leanh::lean_dec_ref(v___y_5043_);
    crate::leanh::lean_dec(v___y_5042_);
    crate::leanh::lean_dec_ref(v___y_5041_);
    crate::leanh::lean_dec(v___y_5040_);
    crate::leanh::lean_dec_ref(v___y_5039_);
    crate::leanh::lean_dec(v___y_5038_);
    return v_res_5046_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(
    mut v_as_5047_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5048_: *mut crate::leanh::LeanObject,
    mut v_b_5049_: *mut crate::leanh::LeanObject,
    mut v_a_5050_: *mut crate::leanh::LeanObject,
    mut v___y_5051_: *mut crate::leanh::LeanObject,
    mut v___y_5052_: *mut crate::leanh::LeanObject,
    mut v___y_5053_: *mut crate::leanh::LeanObject,
    mut v___y_5054_: *mut crate::leanh::LeanObject,
    mut v___y_5055_: *mut crate::leanh::LeanObject,
    mut v___y_5056_: *mut crate::leanh::LeanObject,
    mut v___y_5057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5059_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___redArg(v_as_x27_5048_, v_b_5049_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_);
    return v___x_5059_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3___boxed(
    mut v_as_5060_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5061_: *mut crate::leanh::LeanObject,
    mut v_b_5062_: *mut crate::leanh::LeanObject,
    mut v_a_5063_: *mut crate::leanh::LeanObject,
    mut v___y_5064_: *mut crate::leanh::LeanObject,
    mut v___y_5065_: *mut crate::leanh::LeanObject,
    mut v___y_5066_: *mut crate::leanh::LeanObject,
    mut v___y_5067_: *mut crate::leanh::LeanObject,
    mut v___y_5068_: *mut crate::leanh::LeanObject,
    mut v___y_5069_: *mut crate::leanh::LeanObject,
    mut v___y_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5072_ = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__3(v_as_5060_, v_as_x27_5061_, v_b_5062_, v_a_5063_, v___y_5064_, v___y_5065_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_, v___y_5070_);
    crate::leanh::lean_dec(v___y_5070_);
    crate::leanh::lean_dec_ref(v___y_5069_);
    crate::leanh::lean_dec(v___y_5068_);
    crate::leanh::lean_dec_ref(v___y_5067_);
    crate::leanh::lean_dec(v___y_5066_);
    crate::leanh::lean_dec_ref(v___y_5065_);
    crate::leanh::lean_dec(v___y_5064_);
    crate::leanh::lean_dec(v_as_x27_5061_);
    crate::leanh::lean_dec(v_as_5060_);
    return v_res_5072_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(
    mut v_00_u03b1_5073_: *mut crate::leanh::LeanObject,
    mut v_msg_5074_: *mut crate::leanh::LeanObject,
    mut v___y_5075_: *mut crate::leanh::LeanObject,
    mut v___y_5076_: *mut crate::leanh::LeanObject,
    mut v___y_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5083_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v_msg_5074_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
    return v___x_5083_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___boxed(
    mut v_00_u03b1_5084_: *mut crate::leanh::LeanObject,
    mut v_msg_5085_: *mut crate::leanh::LeanObject,
    mut v___y_5086_: *mut crate::leanh::LeanObject,
    mut v___y_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
    mut v___y_5089_: *mut crate::leanh::LeanObject,
    mut v___y_5090_: *mut crate::leanh::LeanObject,
    mut v___y_5091_: *mut crate::leanh::LeanObject,
    mut v___y_5092_: *mut crate::leanh::LeanObject,
    mut v___y_5093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5094_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8(v_00_u03b1_5084_, v_msg_5085_, v___y_5086_, v___y_5087_, v___y_5088_, v___y_5089_, v___y_5090_, v___y_5091_, v___y_5092_);
    crate::leanh::lean_dec(v___y_5092_);
    crate::leanh::lean_dec_ref(v___y_5091_);
    crate::leanh::lean_dec(v___y_5090_);
    crate::leanh::lean_dec_ref(v___y_5089_);
    crate::leanh::lean_dec(v___y_5088_);
    crate::leanh::lean_dec_ref(v___y_5087_);
    crate::leanh::lean_dec(v___y_5086_);
    return v_res_5094_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15(
    mut v_o_5095_: *mut crate::leanh::LeanObject,
    mut v___y_5096_: *mut crate::leanh::LeanObject,
    mut v___y_5097_: *mut crate::leanh::LeanObject,
    mut v___y_5098_: *mut crate::leanh::LeanObject,
    mut v___y_5099_: *mut crate::leanh::LeanObject,
    mut v___y_5100_: *mut crate::leanh::LeanObject,
    mut v___y_5101_: *mut crate::leanh::LeanObject,
    mut v___y_5102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5104_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___redArg(v_o_5095_, v___y_5102_);
    return v___x_5104_;
}
pub unsafe fn l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15___boxed(
    mut v_o_5105_: *mut crate::leanh::LeanObject,
    mut v___y_5106_: *mut crate::leanh::LeanObject,
    mut v___y_5107_: *mut crate::leanh::LeanObject,
    mut v___y_5108_: *mut crate::leanh::LeanObject,
    mut v___y_5109_: *mut crate::leanh::LeanObject,
    mut v___y_5110_: *mut crate::leanh::LeanObject,
    mut v___y_5111_: *mut crate::leanh::LeanObject,
    mut v___y_5112_: *mut crate::leanh::LeanObject,
    mut v___y_5113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5114_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__10_spec__15(v_o_5105_, v___y_5106_, v___y_5107_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
    crate::leanh::lean_dec(v___y_5112_);
    crate::leanh::lean_dec_ref(v___y_5111_);
    crate::leanh::lean_dec(v___y_5110_);
    crate::leanh::lean_dec_ref(v___y_5109_);
    crate::leanh::lean_dec(v___y_5108_);
    crate::leanh::lean_dec_ref(v___y_5107_);
    crate::leanh::lean_dec(v___y_5106_);
    return v_res_5114_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(
    mut v_00_u03b2_5115_: *mut crate::leanh::LeanObject,
    mut v_m_5116_: *mut crate::leanh::LeanObject,
    mut v_a_5117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5118_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___redArg(v_m_5116_, v_a_5117_);
    return v___x_5118_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b2_5119_: *mut crate::leanh::LeanObject,
    mut v_m_5120_: *mut crate::leanh::LeanObject,
    mut v_a_5121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5122_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6(v_00_u03b2_5119_, v_m_5120_, v_a_5121_);
    crate::leanh::lean_dec(v_a_5121_);
    crate::leanh::lean_dec_ref(v_m_5120_);
    return v_res_5122_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(
    mut v_00_u03b2_5123_: *mut crate::leanh::LeanObject,
    mut v_x_5124_: *mut crate::leanh::LeanObject,
    mut v_x_5125_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5126_: u8 = 0;
    v___x_5126_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___redArg(v_x_5124_, v_x_5125_);
    return v___x_5126_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9___boxed(
    mut v_00_u03b2_5127_: *mut crate::leanh::LeanObject,
    mut v_x_5128_: *mut crate::leanh::LeanObject,
    mut v_x_5129_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5130_: u8 = 0;
    let mut v_r_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5130_ = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9(v_00_u03b2_5127_, v_x_5128_, v_x_5129_);
    crate::leanh::lean_dec_ref(v_x_5129_);
    crate::leanh::lean_dec_ref(v_x_5128_);
    v_r_5131_ = crate::leanh::lean_box((v_res_5130_) as usize);
    return v_r_5131_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(
    mut v_00_u03b2_5132_: *mut crate::leanh::LeanObject,
    mut v_a_5133_: *mut crate::leanh::LeanObject,
    mut v_x_5134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5135_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___redArg(v_a_5133_, v_x_5134_);
    return v___x_5135_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12___boxed(
    mut v_00_u03b2_5136_: *mut crate::leanh::LeanObject,
    mut v_a_5137_: *mut crate::leanh::LeanObject,
    mut v_x_5138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5139_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__6_spec__12(v_00_u03b2_5136_, v_a_5137_, v_x_5138_);
    crate::leanh::lean_dec(v_x_5138_);
    crate::leanh::lean_dec(v_a_5137_);
    return v_res_5139_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20(
    mut v_ref_5140_: *mut crate::leanh::LeanObject,
    mut v_msgData_5141_: *mut crate::leanh::LeanObject,
    mut v_severity_5142_: u8,
    mut v_isSilent_5143_: u8,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
    mut v___y_5146_: *mut crate::leanh::LeanObject,
    mut v___y_5147_: *mut crate::leanh::LeanObject,
    mut v___y_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
    mut v___y_5150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5152_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___redArg(v_ref_5140_, v_msgData_5141_, v_severity_5142_, v_isSilent_5143_, v___y_5147_, v___y_5148_, v___y_5149_, v___y_5150_);
    return v___x_5152_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20___boxed(
    mut v_ref_5153_: *mut crate::leanh::LeanObject,
    mut v_msgData_5154_: *mut crate::leanh::LeanObject,
    mut v_severity_5155_: *mut crate::leanh::LeanObject,
    mut v_isSilent_5156_: *mut crate::leanh::LeanObject,
    mut v___y_5157_: *mut crate::leanh::LeanObject,
    mut v___y_5158_: *mut crate::leanh::LeanObject,
    mut v___y_5159_: *mut crate::leanh::LeanObject,
    mut v___y_5160_: *mut crate::leanh::LeanObject,
    mut v___y_5161_: *mut crate::leanh::LeanObject,
    mut v___y_5162_: *mut crate::leanh::LeanObject,
    mut v___y_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_5165_: u8 = 0;
    let mut v_isSilent_boxed_5166_: u8 = 0;
    let mut v_res_5167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_5165_ = (crate::leanh::lean_unbox(v_severity_5155_) as u8);
    v_isSilent_boxed_5166_ = (crate::leanh::lean_unbox(v_isSilent_5156_) as u8);
    v_res_5167_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20(v_ref_5153_, v_msgData_5154_, v_severity_boxed_5165_, v_isSilent_boxed_5166_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
    crate::leanh::lean_dec(v___y_5163_);
    crate::leanh::lean_dec_ref(v___y_5162_);
    crate::leanh::lean_dec(v___y_5161_);
    crate::leanh::lean_dec_ref(v___y_5160_);
    crate::leanh::lean_dec(v___y_5159_);
    crate::leanh::lean_dec_ref(v___y_5158_);
    crate::leanh::lean_dec(v___y_5157_);
    crate::leanh::lean_dec(v_ref_5153_);
    return v_res_5167_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16(
    mut v_00_u03b2_5168_: *mut crate::leanh::LeanObject,
    mut v_x_5169_: *mut crate::leanh::LeanObject,
    mut v_x_5170_: usize,
    mut v_x_5171_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5172_: u8 = 0;
    v___x_5172_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___redArg(v_x_5169_, v_x_5170_, v_x_5171_);
    return v___x_5172_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16___boxed(
    mut v_00_u03b2_5173_: *mut crate::leanh::LeanObject,
    mut v_x_5174_: *mut crate::leanh::LeanObject,
    mut v_x_5175_: *mut crate::leanh::LeanObject,
    mut v_x_5176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_39011__boxed_5177_: usize = 0;
    let mut v_res_5178_: u8 = 0;
    let mut v_r_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_39011__boxed_5177_ = crate::leanh::lean_unbox_usize(v_x_5175_);
    crate::leanh::lean_dec(v_x_5175_);
    v_res_5178_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16(v_00_u03b2_5173_, v_x_5174_, v_x_39011__boxed_5177_, v_x_5176_);
    crate::leanh::lean_dec_ref(v_x_5176_);
    crate::leanh::lean_dec_ref(v_x_5174_);
    v_r_5179_ = crate::leanh::lean_box((v_res_5178_) as usize);
    return v_r_5179_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20(
    mut v_00_u03b2_5180_: *mut crate::leanh::LeanObject,
    mut v_keys_5181_: *mut crate::leanh::LeanObject,
    mut v_vals_5182_: *mut crate::leanh::LeanObject,
    mut v_heq_5183_: *mut crate::leanh::LeanObject,
    mut v_i_5184_: *mut crate::leanh::LeanObject,
    mut v_k_5185_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5186_: u8 = 0;
    v___x_5186_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___redArg(v_keys_5181_, v_i_5184_, v_k_5185_);
    return v___x_5186_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20___boxed(
    mut v_00_u03b2_5187_: *mut crate::leanh::LeanObject,
    mut v_keys_5188_: *mut crate::leanh::LeanObject,
    mut v_vals_5189_: *mut crate::leanh::LeanObject,
    mut v_heq_5190_: *mut crate::leanh::LeanObject,
    mut v_i_5191_: *mut crate::leanh::LeanObject,
    mut v_k_5192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5193_: u8 = 0;
    let mut v_r_5194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5193_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__2_spec__4_spec__9_spec__16_spec__20(v_00_u03b2_5187_, v_keys_5188_, v_vals_5189_, v_heq_5190_, v_i_5191_, v_k_5192_);
    crate::leanh::lean_dec_ref(v_k_5192_);
    crate::leanh::lean_dec_ref(v_vals_5189_);
    crate::leanh::lean_dec_ref(v_keys_5188_);
    v_r_5194_ = crate::leanh::lean_box((v_res_5193_) as usize);
    return v_r_5194_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_runPrecheck(
    mut v_stx_5195_: *mut crate::leanh::LeanObject,
    mut v_a_5196_: *mut crate::leanh::LeanObject,
    mut v_a_5197_: *mut crate::leanh::LeanObject,
    mut v_a_5198_: *mut crate::leanh::LeanObject,
    mut v_a_5199_: *mut crate::leanh::LeanObject,
    mut v_a_5200_: *mut crate::leanh::LeanObject,
    mut v_a_5201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5204_: u8 = 0;
    let mut v___x_5205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5211_: u8 = 0;
    let mut v___x_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5213_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_5209_ = crate::leanh::lean_ctor_get(v_a_5200_, 2);
                v___x_5210_ = l_Lean_Elab_Term_Quotation_quotPrecheck;
                v___x_5211_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_5209_, v___x_5210_);
                if v___x_5211_ == 0 {
                    v___y_5204_ = v___x_5211_;
                    state = 1;
                    continue;
                } else {
                    v___x_5212_ = l_Lean_Elab_Term_Quotation_hygiene;
                    v___x_5213_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_5209_, v___x_5212_);
                    v___y_5204_ = v___x_5213_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_5204_ == 0 {
                    crate::leanh::lean_dec(v_stx_5195_);
                    v___x_5205_ = crate::leanh::lean_box(0);
                    v___x_5206_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5206_, 0, v___x_5205_);
                    return v___x_5206_;
                } else {
                    v___x_5207_ = l_Lean_NameSet_empty;
                    v___x_5208_ = l_Lean_Elab_Term_Quotation_precheck(
                        v_stx_5195_,
                        v___x_5207_,
                        v_a_5196_,
                        v_a_5197_,
                        v_a_5198_,
                        v_a_5199_,
                        v_a_5200_,
                        v_a_5201_,
                    );
                    return v___x_5208_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_runPrecheck___boxed(
    mut v_stx_5214_: *mut crate::leanh::LeanObject,
    mut v_a_5215_: *mut crate::leanh::LeanObject,
    mut v_a_5216_: *mut crate::leanh::LeanObject,
    mut v_a_5217_: *mut crate::leanh::LeanObject,
    mut v_a_5218_: *mut crate::leanh::LeanObject,
    mut v_a_5219_: *mut crate::leanh::LeanObject,
    mut v_a_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5222_ = l_Lean_Elab_Term_Quotation_runPrecheck(
        v_stx_5214_,
        v_a_5215_,
        v_a_5216_,
        v_a_5217_,
        v_a_5218_,
        v_a_5219_,
        v_a_5220_,
    );
    crate::leanh::lean_dec(v_a_5220_);
    crate::leanh::lean_dec_ref(v_a_5219_);
    crate::leanh::lean_dec(v_a_5218_);
    crate::leanh::lean_dec_ref(v_a_5217_);
    crate::leanh::lean_dec(v_a_5216_);
    crate::leanh::lean_dec_ref(v_a_5215_);
    return v_res_5222_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(
    mut v_e_5226_: *mut crate::leanh::LeanObject,
    mut v_init_5227_: *mut crate::leanh::LeanObject,
    mut v_x_5228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_5230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5235_: u8 = 0;
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: u8 = 0;
    let mut v___x_5238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5246_: u8 = 0;
    let mut v_unused_5247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5228_) == 0 {
                    v_v_5229_ = crate::leanh::lean_ctor_get(v_x_5228_, 2);
                    v_l_5230_ = crate::leanh::lean_ctor_get(v_x_5228_, 3);
                    v_r_5231_ = crate::leanh::lean_ctor_get(v_x_5228_, 4);
                    v___x_5232_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_5226_, v_init_5227_, v_l_5230_);
                    if crate::leanh::lean_obj_tag(v___x_5232_) == 0 {
                        return v___x_5232_;
                    } else {
                        v_isSharedCheck_5246_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5232_)) as u8;
                        if v_isSharedCheck_5246_ == 0 {
                            v_unused_5247_ = crate::leanh::lean_ctor_get(v___x_5232_, 0);
                            crate::leanh::lean_dec(v_unused_5247_);
                            v___x_5234_ = v___x_5232_;
                            v_isShared_5235_ = v_isSharedCheck_5246_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_5232_);
                            v___x_5234_ = crate::leanh::lean_box(0);
                            v_isShared_5235_ = v_isSharedCheck_5246_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_5248_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5248_, 0, v_init_5227_);
                    return v___x_5248_;
                }
            }
            1 => {
                v___x_5236_ = crate::leanh::lean_box(0);
                v___x_5237_ = lean_expr_eqv(v_e_5226_, v_v_5229_);
                if v___x_5237_ == 0 {
                    crate::leanh::lean_del_object(v___x_5234_);
                    v___x_5238_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0;
                    v_init_5227_ = v___x_5238_;
                    v_x_5228_ = v_r_5231_;
                    state = 0;
                    continue;
                } else {
                    v___x_5240_ = crate::leanh::lean_box((v___x_5237_) as usize);
                    v___x_5241_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5241_, 0, v___x_5240_);
                    v___x_5242_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5242_, 0, v___x_5241_);
                    crate::leanh::lean_ctor_set(v___x_5242_, 1, v___x_5236_);
                    if v_isShared_5235_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5234_, 0);
                        crate::leanh::lean_ctor_set(v___x_5234_, 0, v___x_5242_);
                        v___x_5244_ = v___x_5234_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5245_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5245_, 0, v___x_5242_);
                        v___x_5244_ = v_reuseFailAlloc_5245_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5244_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___boxed(
    mut v_e_5249_: *mut crate::leanh::LeanObject,
    mut v_init_5250_: *mut crate::leanh::LeanObject,
    mut v_x_5251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5252_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_5249_, v_init_5250_, v_x_5251_);
    crate::leanh::lean_dec(v_x_5251_);
    crate::leanh::lean_dec_ref(v_e_5249_);
    return v_res_5252_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(
    mut v_e_5253_: *mut crate::leanh::LeanObject,
    mut v_a_5254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut v___x_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5265_: u8 = 0;
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5269_: u8 = 0;
    let mut v_sectionFVars_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sectionFVars_5270_ = crate::leanh::lean_ctor_get(v_a_5254_, 5);
                v___x_5271_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0___closed__0;
                v___x_5272_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable_spec__0(v_e_5253_, v___x_5271_, v_sectionFVars_5270_);
                v_a_5273_ = crate::leanh::lean_ctor_get(v___x_5272_, 0);
                crate::leanh::lean_inc(v_a_5273_);
                crate::leanh::lean_dec_ref(v___x_5272_);
                v___y_5257_ = v_a_5273_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_5258_ = crate::leanh::lean_ctor_get(v___y_5257_, 0);
                crate::leanh::lean_inc(v_fst_5258_);
                crate::leanh::lean_dec_ref(v___y_5257_);
                if crate::leanh::lean_obj_tag(v_fst_5258_) == 0 {
                    v___x_5259_ = 0;
                    v___x_5260_ = crate::leanh::lean_box((v___x_5259_) as usize);
                    v___x_5261_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5261_, 0, v___x_5260_);
                    return v___x_5261_;
                } else {
                    v_val_5262_ = crate::leanh::lean_ctor_get(v_fst_5258_, 0);
                    v_isSharedCheck_5269_ = (!crate::leanh::lean_is_exclusive(v_fst_5258_)) as u8;
                    if v_isSharedCheck_5269_ == 0 {
                        v___x_5264_ = v_fst_5258_;
                        v_isShared_5265_ = v_isSharedCheck_5269_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5262_);
                        crate::leanh::lean_dec(v_fst_5258_);
                        v___x_5264_ = crate::leanh::lean_box(0);
                        v_isShared_5265_ = v_isSharedCheck_5269_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5265_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5264_, 0);
                    v___x_5267_ = v___x_5264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5268_, 0, v_val_5262_);
                    v___x_5267_ = v_reuseFailAlloc_5268_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5267_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg___boxed(
    mut v_e_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_a_5276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5277_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_5274_, v_a_5275_);
    crate::leanh::lean_dec_ref(v_a_5275_);
    crate::leanh::lean_dec_ref(v_e_5274_);
    return v_res_5277_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(
    mut v_e_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
    mut v_a_5280_: *mut crate::leanh::LeanObject,
    mut v_a_5281_: *mut crate::leanh::LeanObject,
    mut v_a_5282_: *mut crate::leanh::LeanObject,
    mut v_a_5283_: *mut crate::leanh::LeanObject,
    mut v_a_5284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5286_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_e_5278_, v_a_5279_);
    return v___x_5286_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___boxed(
    mut v_e_5287_: *mut crate::leanh::LeanObject,
    mut v_a_5288_: *mut crate::leanh::LeanObject,
    mut v_a_5289_: *mut crate::leanh::LeanObject,
    mut v_a_5290_: *mut crate::leanh::LeanObject,
    mut v_a_5291_: *mut crate::leanh::LeanObject,
    mut v_a_5292_: *mut crate::leanh::LeanObject,
    mut v_a_5293_: *mut crate::leanh::LeanObject,
    mut v_a_5294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5295_ =
        l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable(
            v_e_5287_, v_a_5288_, v_a_5289_, v_a_5290_, v_a_5291_, v_a_5292_, v_a_5293_,
        );
    crate::leanh::lean_dec(v_a_5293_);
    crate::leanh::lean_dec_ref(v_a_5292_);
    crate::leanh::lean_dec(v_a_5291_);
    crate::leanh::lean_dec_ref(v_a_5290_);
    crate::leanh::lean_dec(v_a_5289_);
    crate::leanh::lean_dec_ref(v_a_5288_);
    crate::leanh::lean_dec_ref(v_e_5287_);
    return v_res_5295_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(
    mut v_as_x27_5304_: *mut crate::leanh::LeanObject,
    mut v_b_5305_: *mut crate::leanh::LeanObject,
    mut v___y_5306_: *mut crate::leanh::LeanObject,
    mut v___y_5307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___y_5320_: u8 = 0;
    let mut v___x_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: u8 = 0;
    let mut v___x_5329_: u8 = 0;
    let mut v_isSharedCheck_5330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_x27_5304_) == 0 {
                    v___x_5309_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5309_, 0, v_b_5305_);
                    return v___x_5309_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5305_);
                    v_head_5310_ = crate::leanh::lean_ctor_get(v_as_x27_5304_, 0);
                    v_tail_5311_ = crate::leanh::lean_ctor_get(v_as_x27_5304_, 1);
                    v_fst_5312_ = crate::leanh::lean_ctor_get(v_head_5310_, 0);
                    v___x_5313_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0;
                    if crate::leanh::lean_obj_tag(v_fst_5312_) == 1 {
                        v___x_5314_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_isSectionVariable___redArg(v_fst_5312_, v___y_5306_);
                        v_a_5315_ = crate::leanh::lean_ctor_get(v___x_5314_, 0);
                        v_isSharedCheck_5330_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5314_)) as u8;
                        if v_isSharedCheck_5330_ == 0 {
                            v___x_5317_ = v___x_5314_;
                            v_isShared_5318_ = v_isSharedCheck_5330_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5315_);
                            crate::leanh::lean_dec(v___x_5314_);
                            v___x_5317_ = crate::leanh::lean_box(0);
                            v_isShared_5318_ = v_isSharedCheck_5330_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_as_x27_5304_ = v_tail_5311_;
                        v_b_5305_ = v___x_5313_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                v_options_5326_ = crate::leanh::lean_ctor_get(v___y_5307_, 2);
                v___x_5327_ = l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars;
                v___x_5328_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Linter_logLint___at___00Lean_Linter_logLintIf___at___00Lean_Elab_Term_Quotation_precheck_spec__2_spec__11_spec__17_spec__20_spec__22(v_options_5326_, v___x_5327_);
                if v___x_5328_ == 0 {
                    crate::leanh::lean_dec(v_a_5315_);
                    v___y_5320_ = v___x_5328_;
                    state = 2;
                    continue;
                } else {
                    v___x_5329_ = (crate::leanh::lean_unbox(v_a_5315_) as u8);
                    crate::leanh::lean_dec(v_a_5315_);
                    v___y_5320_ = v___x_5329_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_5320_ == 0 {
                    crate::leanh::lean_del_object(v___x_5317_);
                    v_as_x27_5304_ = v_tail_5311_;
                    v_b_5305_ = v___x_5313_;
                    state = 0;
                    continue;
                } else {
                    v___x_5322_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__2;
                    if v_isShared_5318_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5317_, 0, v___x_5322_);
                        v___x_5324_ = v___x_5317_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5325_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
                        v___x_5324_ = v_reuseFailAlloc_5325_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5324_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___boxed(
    mut v_as_x27_5332_: *mut crate::leanh::LeanObject,
    mut v_b_5333_: *mut crate::leanh::LeanObject,
    mut v___y_5334_: *mut crate::leanh::LeanObject,
    mut v___y_5335_: *mut crate::leanh::LeanObject,
    mut v___y_5336_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5337_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(
            v_as_x27_5332_,
            v_b_5333_,
            v___y_5334_,
            v___y_5335_,
        );
    crate::leanh::lean_dec_ref(v___y_5335_);
    crate::leanh::lean_dec_ref(v___y_5334_);
    crate::leanh::lean_dec(v_as_x27_5332_);
    return v_res_5337_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5339_ = l_Lean_Elab_Term_Quotation_precheckIdent___closed__0;
    v___x_5340_ = l_Lean_stringToMessageData(v___x_5339_);
    return v___x_5340_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5342_ = l_Lean_Elab_Term_Quotation_precheckIdent___closed__2;
    v___x_5343_ = l_Lean_stringToMessageData(v___x_5342_);
    return v___x_5343_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5347_ = l_Lean_Elab_Term_Quotation_precheckIdent___closed__5;
    v___x_5348_ = l_Lean_MessageData_ofFormat(v___x_5347_);
    return v___x_5348_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5349_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__6_once),
        _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__6,
    );
    v___x_5350_ = l_Lean_MessageData_note(v___x_5349_);
    return v___x_5350_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckIdent(
    mut v_stx_5351_: *mut crate::leanh::LeanObject,
    mut v_a_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
    mut v_a_5355_: *mut crate::leanh::LeanObject,
    mut v_a_5356_: *mut crate::leanh::LeanObject,
    mut v_a_5357_: *mut crate::leanh::LeanObject,
    mut v_a_5358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_5360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_preresolved_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v_fst_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5373_: u8 = 0;
    let mut v___x_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5388_: u8 = 0;
    let mut v_unused_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5390_: u8 = 0;
    let mut v_a_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5398_: u8 = 0;
    let mut v___y_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5405_: u8 = 0;
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut v___x_5410_: u8 = 0;
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5417_: u8 = 0;
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: u8 = 0;
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5428_: u8 = 0;
    let mut v___x_5429_: u8 = 0;
    let mut v___x_5430_: u8 = 0;
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5435_: u8 = 0;
    let mut v_a_5436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5439_: u8 = 0;
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5443_: u8 = 0;
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_stx_5351_) == 3 {
                    v_val_5360_ = crate::leanh::lean_ctor_get(v_stx_5351_, 2);
                    crate::leanh::lean_inc(v_val_5360_);
                    v_preresolved_5361_ = crate::leanh::lean_ctor_get(v_stx_5351_, 3);
                    v___x_5410_ = l_List_isEmpty___redArg(v_preresolved_5361_);
                    if v___x_5410_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_stx_5351_, 4);
                        crate::leanh::lean_dec(v_val_5360_);
                        v___x_5411_ = crate::leanh::lean_box(0);
                        v___x_5412_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5412_, 0, v___x_5411_);
                        return v___x_5412_;
                    } else {
                        crate::leanh::lean_inc(v_val_5360_);
                        crate::leanh::lean_inc_ref(v_stx_5351_);
                        v___x_5413_ = l_Lean_Elab_realizeGlobalNameWithInfos(
                            v_stx_5351_,
                            v_val_5360_,
                            v_a_5357_,
                            v_a_5358_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5413_) == 0 {
                            v_a_5414_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
                            v_isSharedCheck_5435_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5413_)) as u8;
                            if v_isSharedCheck_5435_ == 0 {
                                v___x_5416_ = v___x_5413_;
                                v_isShared_5417_ = v_isSharedCheck_5435_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5414_);
                                crate::leanh::lean_dec(v___x_5413_);
                                v___x_5416_ = crate::leanh::lean_box(0);
                                v_isShared_5417_ = v_isSharedCheck_5435_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_stx_5351_, 4);
                            crate::leanh::lean_dec(v_val_5360_);
                            v_a_5436_ = crate::leanh::lean_ctor_get(v___x_5413_, 0);
                            v_isSharedCheck_5443_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5413_)) as u8;
                            if v_isSharedCheck_5443_ == 0 {
                                v___x_5438_ = v___x_5413_;
                                v_isShared_5439_ = v_isSharedCheck_5443_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5436_);
                                crate::leanh::lean_dec(v___x_5413_);
                                v___x_5438_ = crate::leanh::lean_box(0);
                                v_isShared_5439_ = v_isSharedCheck_5443_;
                                state = 15;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_stx_5351_);
                    v___x_5444_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
                    return v___x_5444_;
                }
            }
            1 => {
                v___x_5364_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg___closed__0;
                v___x_5365_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(v_a_5363_, v___x_5364_, v_a_5353_, v_a_5357_);
                crate::leanh::lean_dec(v_a_5363_);
                if crate::leanh::lean_obj_tag(v___x_5365_) == 0 {
                    v_a_5366_ = crate::leanh::lean_ctor_get(v___x_5365_, 0);
                    v_isSharedCheck_5390_ = (!crate::leanh::lean_is_exclusive(v___x_5365_)) as u8;
                    if v_isSharedCheck_5390_ == 0 {
                        v___x_5368_ = v___x_5365_;
                        v_isShared_5369_ = v_isSharedCheck_5390_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5366_);
                        crate::leanh::lean_dec(v___x_5365_);
                        v___x_5368_ = crate::leanh::lean_box(0);
                        v_isShared_5369_ = v_isSharedCheck_5390_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_val_5360_);
                    v_a_5391_ = crate::leanh::lean_ctor_get(v___x_5365_, 0);
                    v_isSharedCheck_5398_ = (!crate::leanh::lean_is_exclusive(v___x_5365_)) as u8;
                    if v_isSharedCheck_5398_ == 0 {
                        v___x_5393_ = v___x_5365_;
                        v_isShared_5394_ = v_isSharedCheck_5398_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5391_);
                        crate::leanh::lean_dec(v___x_5365_);
                        v___x_5393_ = crate::leanh::lean_box(0);
                        v_isShared_5394_ = v_isSharedCheck_5398_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_5370_ = crate::leanh::lean_ctor_get(v_a_5366_, 0);
                v_isSharedCheck_5388_ = (!crate::leanh::lean_is_exclusive(v_a_5366_)) as u8;
                if v_isSharedCheck_5388_ == 0 {
                    v_unused_5389_ = crate::leanh::lean_ctor_get(v_a_5366_, 1);
                    crate::leanh::lean_dec(v_unused_5389_);
                    v___x_5372_ = v_a_5366_;
                    v_isShared_5373_ = v_isSharedCheck_5388_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_5370_);
                    crate::leanh::lean_dec(v_a_5366_);
                    v___x_5372_ = crate::leanh::lean_box(0);
                    v_isShared_5373_ = v_isSharedCheck_5388_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_fst_5370_) == 0 {
                    crate::leanh::lean_del_object(v___x_5368_);
                    v___x_5374_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Quotation_precheckIdent___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Quotation_precheckIdent___closed__1_once
                        ),
                        _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__1,
                    );
                    v___x_5375_ = l_Lean_MessageData_ofName(v_val_5360_);
                    if v_isShared_5373_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5372_, 7);
                        crate::leanh::lean_ctor_set(v___x_5372_, 1, v___x_5375_);
                        crate::leanh::lean_ctor_set(v___x_5372_, 0, v___x_5374_);
                        v___x_5377_ = v___x_5372_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5383_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5374_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5383_, 1, v___x_5375_);
                        v___x_5377_ = v_reuseFailAlloc_5383_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5372_);
                    crate::leanh::lean_dec(v_val_5360_);
                    v_val_5384_ = crate::leanh::lean_ctor_get(v_fst_5370_, 0);
                    crate::leanh::lean_inc(v_val_5384_);
                    crate::leanh::lean_dec_ref_known(v_fst_5370_, 1);
                    if v_isShared_5369_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5368_, 0, v_val_5384_);
                        v___x_5386_ = v___x_5368_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5387_, 0, v_val_5384_);
                        v___x_5386_ = v_reuseFailAlloc_5387_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5378_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_Quotation_precheckIdent___closed__3_once
                    ),
                    _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__3,
                );
                v___x_5379_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5379_, 0, v___x_5377_);
                crate::leanh::lean_ctor_set(v___x_5379_, 1, v___x_5378_);
                v___x_5380_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Term_Quotation_precheckIdent___closed__7),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Term_Quotation_precheckIdent___closed__7_once
                    ),
                    _init_l_Lean_Elab_Term_Quotation_precheckIdent___closed__7,
                );
                v___x_5381_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5381_, 0, v___x_5379_);
                crate::leanh::lean_ctor_set(v___x_5381_, 1, v___x_5380_);
                v___x_5382_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1_spec__8___redArg(v___x_5381_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
                return v___x_5382_;
            }
            5 => {
                return v___x_5386_;
            }
            6 => {
                if v_isShared_5394_ == 0 {
                    v___x_5396_ = v___x_5393_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5397_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_a_5391_);
                    v___x_5396_ = v_reuseFailAlloc_5397_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5396_;
            }
            8 => {
                if crate::leanh::lean_obj_tag(v___y_5400_) == 0 {
                    v_a_5401_ = crate::leanh::lean_ctor_get(v___y_5400_, 0);
                    crate::leanh::lean_inc(v_a_5401_);
                    crate::leanh::lean_dec_ref_known(v___y_5400_, 1);
                    v_a_5363_ = v_a_5401_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5360_);
                    v_a_5402_ = crate::leanh::lean_ctor_get(v___y_5400_, 0);
                    v_isSharedCheck_5409_ = (!crate::leanh::lean_is_exclusive(v___y_5400_)) as u8;
                    if v_isSharedCheck_5409_ == 0 {
                        v___x_5404_ = v___y_5400_;
                        v_isShared_5405_ = v_isSharedCheck_5409_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5402_);
                        crate::leanh::lean_dec(v___y_5400_);
                        v___x_5404_ = crate::leanh::lean_box(0);
                        v_isShared_5405_ = v_isSharedCheck_5409_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_5405_ == 0 {
                    v___x_5407_ = v___x_5404_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5408_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5408_, 0, v_a_5402_);
                    v___x_5407_ = v_reuseFailAlloc_5408_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5407_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v_a_5414_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_a_5414_, 2);
                    crate::leanh::lean_dec_ref_known(v_stx_5351_, 4);
                    crate::leanh::lean_dec(v_val_5360_);
                    v___x_5418_ = crate::leanh::lean_box(0);
                    if v_isShared_5417_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5416_, 0, v___x_5418_);
                        v___x_5420_ = v___x_5416_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_5421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5421_, 0, v___x_5418_);
                        v___x_5420_ = v_reuseFailAlloc_5421_;
                        state = 12;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5414_);
                    v___x_5422_ = l_Lean_NameSet_contains(v_a_5352_, v_val_5360_);
                    if v___x_5422_ == 0 {
                        crate::leanh::lean_del_object(v___x_5416_);
                        v___x_5423_ = crate::leanh::lean_box(0);
                        v___x_5424_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_val_5360_);
                        v___x_5425_ = l_Lean_Elab_Term_resolveName(
                            v_stx_5351_,
                            v_val_5360_,
                            v___x_5423_,
                            v___x_5423_,
                            v___x_5424_,
                            v_a_5353_,
                            v_a_5354_,
                            v_a_5355_,
                            v_a_5356_,
                            v_a_5357_,
                            v_a_5358_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5425_) == 0 {
                            v___y_5400_ = v___x_5425_;
                            state = 8;
                            continue;
                        } else {
                            v_a_5426_ = crate::leanh::lean_ctor_get(v___x_5425_, 0);
                            crate::leanh::lean_inc(v_a_5426_);
                            v___x_5429_ = l_Lean_Exception_isInterrupt(v_a_5426_);
                            if v___x_5429_ == 0 {
                                v___x_5430_ = l_Lean_Exception_isRuntime(v_a_5426_);
                                v___y_5428_ = v___x_5430_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_5426_);
                                v___y_5428_ = v___x_5429_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_stx_5351_, 4);
                        crate::leanh::lean_dec(v_val_5360_);
                        v___x_5431_ = crate::leanh::lean_box(0);
                        if v_isShared_5417_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5416_, 0, v___x_5431_);
                            v___x_5433_ = v___x_5416_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_5434_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5434_, 0, v___x_5431_);
                            v___x_5433_ = v_reuseFailAlloc_5434_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            12 => {
                return v___x_5420_;
            }
            13 => {
                if v___y_5428_ == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5425_, 1);
                    v_a_5363_ = v___x_5423_;
                    state = 1;
                    continue;
                } else {
                    v___y_5400_ = v___x_5425_;
                    state = 8;
                    continue;
                }
            }
            14 => {
                return v___x_5433_;
            }
            15 => {
                if v_isShared_5439_ == 0 {
                    v___x_5441_ = v___x_5438_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5442_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5442_, 0, v_a_5436_);
                    v___x_5441_ = v_reuseFailAlloc_5442_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckIdent___boxed(
    mut v_stx_5445_: *mut crate::leanh::LeanObject,
    mut v_a_5446_: *mut crate::leanh::LeanObject,
    mut v_a_5447_: *mut crate::leanh::LeanObject,
    mut v_a_5448_: *mut crate::leanh::LeanObject,
    mut v_a_5449_: *mut crate::leanh::LeanObject,
    mut v_a_5450_: *mut crate::leanh::LeanObject,
    mut v_a_5451_: *mut crate::leanh::LeanObject,
    mut v_a_5452_: *mut crate::leanh::LeanObject,
    mut v_a_5453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5454_ = l_Lean_Elab_Term_Quotation_precheckIdent(
        v_stx_5445_,
        v_a_5446_,
        v_a_5447_,
        v_a_5448_,
        v_a_5449_,
        v_a_5450_,
        v_a_5451_,
        v_a_5452_,
    );
    crate::leanh::lean_dec(v_a_5452_);
    crate::leanh::lean_dec_ref(v_a_5451_);
    crate::leanh::lean_dec(v_a_5450_);
    crate::leanh::lean_dec_ref(v_a_5449_);
    crate::leanh::lean_dec(v_a_5448_);
    crate::leanh::lean_dec_ref(v_a_5447_);
    crate::leanh::lean_dec(v_a_5446_);
    return v_res_5454_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(
    mut v_as_5455_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5456_: *mut crate::leanh::LeanObject,
    mut v_b_5457_: *mut crate::leanh::LeanObject,
    mut v_a_5458_: *mut crate::leanh::LeanObject,
    mut v___y_5459_: *mut crate::leanh::LeanObject,
    mut v___y_5460_: *mut crate::leanh::LeanObject,
    mut v___y_5461_: *mut crate::leanh::LeanObject,
    mut v___y_5462_: *mut crate::leanh::LeanObject,
    mut v___y_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5467_ =
        l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___redArg(
            v_as_x27_5456_,
            v_b_5457_,
            v___y_5460_,
            v___y_5464_,
        );
    return v___x_5467_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0___boxed(
    mut v_as_5468_: *mut crate::leanh::LeanObject,
    mut v_as_x27_5469_: *mut crate::leanh::LeanObject,
    mut v_b_5470_: *mut crate::leanh::LeanObject,
    mut v_a_5471_: *mut crate::leanh::LeanObject,
    mut v___y_5472_: *mut crate::leanh::LeanObject,
    mut v___y_5473_: *mut crate::leanh::LeanObject,
    mut v___y_5474_: *mut crate::leanh::LeanObject,
    mut v___y_5475_: *mut crate::leanh::LeanObject,
    mut v___y_5476_: *mut crate::leanh::LeanObject,
    mut v___y_5477_: *mut crate::leanh::LeanObject,
    mut v___y_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5480_ = l_List_forIn_x27_loop___at___00Lean_Elab_Term_Quotation_precheckIdent_spec__0(
        v_as_5468_,
        v_as_x27_5469_,
        v_b_5470_,
        v_a_5471_,
        v___y_5472_,
        v___y_5473_,
        v___y_5474_,
        v___y_5475_,
        v___y_5476_,
        v___y_5477_,
        v___y_5478_,
    );
    crate::leanh::lean_dec(v___y_5478_);
    crate::leanh::lean_dec_ref(v___y_5477_);
    crate::leanh::lean_dec(v___y_5476_);
    crate::leanh::lean_dec_ref(v___y_5475_);
    crate::leanh::lean_dec(v___y_5474_);
    crate::leanh::lean_dec_ref(v___y_5473_);
    crate::leanh::lean_dec(v___y_5472_);
    crate::leanh::lean_dec(v_as_x27_5469_);
    crate::leanh::lean_dec(v_as_5468_);
    return v_res_5480_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5492_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_5493_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__1;
    v___x_5494_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___closed__3;
    v___x_5495_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckIdent___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5496_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5492_,
        v___x_5493_,
        v___x_5494_,
        v___x_5495_,
    );
    return v___x_5496_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1___boxed(
    mut v_a_5497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5498_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
    return v_res_5498_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(
    mut v_as_5512_: *mut crate::leanh::LeanObject,
    mut v_sz_5513_: usize,
    mut v_i_5514_: usize,
    mut v_b_5515_: *mut crate::leanh::LeanObject,
    mut v___y_5516_: *mut crate::leanh::LeanObject,
    mut v___y_5517_: *mut crate::leanh::LeanObject,
    mut v___y_5518_: *mut crate::leanh::LeanObject,
    mut v___y_5519_: *mut crate::leanh::LeanObject,
    mut v___y_5520_: *mut crate::leanh::LeanObject,
    mut v___y_5521_: *mut crate::leanh::LeanObject,
    mut v___y_5522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5526_: usize = 0;
    let mut v___x_5527_: usize = 0;
    let mut v___x_5529_: u8 = 0;
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: u8 = 0;
    let mut v___x_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5536_: u8 = 0;
    let mut v___x_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5529_ = lean_usize_dec_lt(v_i_5514_, v_sz_5513_);
                if v___x_5529_ == 0 {
                    v___x_5530_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5530_, 0, v_b_5515_);
                    return v___x_5530_;
                } else {
                    v___x_5531_ = crate::leanh::lean_box(0);
                    v_a_5532_ = lean_array_uget_borrowed(v_as_5512_, v_i_5514_);
                    v___x_5533_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__2;
                    crate::leanh::lean_inc(v_a_5532_);
                    v___x_5534_ = l_Lean_Syntax_isOfKind(v_a_5532_, v___x_5533_);
                    if v___x_5534_ == 0 {
                        v___x_5535_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___closed__4;
                        crate::leanh::lean_inc(v_a_5532_);
                        v___x_5536_ = l_Lean_Syntax_isOfKind(v_a_5532_, v___x_5535_);
                        if v___x_5536_ == 0 {
                            crate::leanh::lean_inc(v_a_5532_);
                            v___x_5537_ = l_Lean_Elab_Term_Quotation_precheck(
                                v_a_5532_,
                                v___y_5516_,
                                v___y_5517_,
                                v___y_5518_,
                                v___y_5519_,
                                v___y_5520_,
                                v___y_5521_,
                                v___y_5522_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5537_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5537_, 1);
                                v_a_5525_ = v___x_5531_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_5537_;
                            }
                        } else {
                            v_a_5525_ = v___x_5531_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_5538_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_5539_ = l_Lean_Syntax_getArg(v_a_5532_, v___x_5538_);
                        v___x_5540_ = l_Lean_Elab_Term_Quotation_precheck(
                            v___x_5539_,
                            v___y_5516_,
                            v___y_5517_,
                            v___y_5518_,
                            v___y_5519_,
                            v___y_5520_,
                            v___y_5521_,
                            v___y_5522_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5540_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5540_, 1);
                            v_a_5525_ = v___x_5531_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_5540_;
                        }
                    }
                }
            }
            1 => {
                v___x_5526_ = 1usize;
                v___x_5527_ = lean_usize_add(v_i_5514_, v___x_5526_);
                v_i_5514_ = v___x_5527_;
                v_b_5515_ = v_a_5525_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0___boxed(
    mut v_as_5541_: *mut crate::leanh::LeanObject,
    mut v_sz_5542_: *mut crate::leanh::LeanObject,
    mut v_i_5543_: *mut crate::leanh::LeanObject,
    mut v_b_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
    mut v___y_5546_: *mut crate::leanh::LeanObject,
    mut v___y_5547_: *mut crate::leanh::LeanObject,
    mut v___y_5548_: *mut crate::leanh::LeanObject,
    mut v___y_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5553_: usize = 0;
    let mut v_i_boxed_5554_: usize = 0;
    let mut v_res_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5553_ = crate::leanh::lean_unbox_usize(v_sz_5542_);
    crate::leanh::lean_dec(v_sz_5542_);
    v_i_boxed_5554_ = crate::leanh::lean_unbox_usize(v_i_5543_);
    crate::leanh::lean_dec(v_i_5543_);
    v_res_5555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_as_5541_, v_sz_boxed_5553_, v_i_boxed_5554_, v_b_5544_, v___y_5545_, v___y_5546_, v___y_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
    crate::leanh::lean_dec(v___y_5551_);
    crate::leanh::lean_dec_ref(v___y_5550_);
    crate::leanh::lean_dec(v___y_5549_);
    crate::leanh::lean_dec_ref(v___y_5548_);
    crate::leanh::lean_dec(v___y_5547_);
    crate::leanh::lean_dec_ref(v___y_5546_);
    crate::leanh::lean_dec(v___y_5545_);
    crate::leanh::lean_dec_ref(v_as_5541_);
    return v_res_5555_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckApp(
    mut v_x_5562_: *mut crate::leanh::LeanObject,
    mut v_a_5563_: *mut crate::leanh::LeanObject,
    mut v_a_5564_: *mut crate::leanh::LeanObject,
    mut v_a_5565_: *mut crate::leanh::LeanObject,
    mut v_a_5566_: *mut crate::leanh::LeanObject,
    mut v_a_5567_: *mut crate::leanh::LeanObject,
    mut v_a_5568_: *mut crate::leanh::LeanObject,
    mut v_a_5569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: u8 = 0;
    let mut v___x_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5581_: usize = 0;
    let mut v___x_5582_: usize = 0;
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut v_unused_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5571_ = l_Lean_Elab_Term_Quotation_precheckApp___closed__1;
                crate::leanh::lean_inc(v_x_5562_);
                v___x_5572_ = l_Lean_Syntax_isOfKind(v_x_5562_, v___x_5571_);
                if v___x_5572_ == 0 {
                    crate::leanh::lean_dec(v_x_5562_);
                    v___x_5573_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
                    return v___x_5573_;
                } else {
                    v___x_5574_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5575_ = l_Lean_Syntax_getArg(v_x_5562_, v___x_5574_);
                    v___x_5576_ = l_Lean_Elab_Term_Quotation_precheck(
                        v___x_5575_,
                        v_a_5563_,
                        v_a_5564_,
                        v_a_5565_,
                        v_a_5566_,
                        v_a_5567_,
                        v_a_5568_,
                        v_a_5569_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5576_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5576_, 1);
                        v___x_5577_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5578_ = l_Lean_Syntax_getArg(v_x_5562_, v___x_5577_);
                        crate::leanh::lean_dec(v_x_5562_);
                        v_args_5579_ = l_Lean_Syntax_getArgs(v___x_5578_);
                        crate::leanh::lean_dec(v___x_5578_);
                        v___x_5580_ = crate::leanh::lean_box(0);
                        v_sz_5581_ = lean_array_size(v_args_5579_);
                        v___x_5582_ = 0usize;
                        v___x_5583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Term_Quotation_precheckApp_spec__0(v_args_5579_, v_sz_5581_, v___x_5582_, v___x_5580_, v_a_5563_, v_a_5564_, v_a_5565_, v_a_5566_, v_a_5567_, v_a_5568_, v_a_5569_);
                        crate::leanh::lean_dec_ref(v_args_5579_);
                        if crate::leanh::lean_obj_tag(v___x_5583_) == 0 {
                            v_isSharedCheck_5590_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5583_)) as u8;
                            if v_isSharedCheck_5590_ == 0 {
                                v_unused_5591_ = crate::leanh::lean_ctor_get(v___x_5583_, 0);
                                crate::leanh::lean_dec(v_unused_5591_);
                                v___x_5585_ = v___x_5583_;
                                v_isShared_5586_ = v_isSharedCheck_5590_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5583_);
                                v___x_5585_ = crate::leanh::lean_box(0);
                                v_isShared_5586_ = v_isSharedCheck_5590_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_5583_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_x_5562_);
                        return v___x_5576_;
                    }
                }
            }
            1 => {
                if v_isShared_5586_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5585_, 0, v___x_5580_);
                    v___x_5588_ = v___x_5585_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v___x_5580_);
                    v___x_5588_ = v_reuseFailAlloc_5589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckApp___boxed(
    mut v_x_5592_: *mut crate::leanh::LeanObject,
    mut v_a_5593_: *mut crate::leanh::LeanObject,
    mut v_a_5594_: *mut crate::leanh::LeanObject,
    mut v_a_5595_: *mut crate::leanh::LeanObject,
    mut v_a_5596_: *mut crate::leanh::LeanObject,
    mut v_a_5597_: *mut crate::leanh::LeanObject,
    mut v_a_5598_: *mut crate::leanh::LeanObject,
    mut v_a_5599_: *mut crate::leanh::LeanObject,
    mut v_a_5600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5601_ = l_Lean_Elab_Term_Quotation_precheckApp(
        v_x_5592_, v_a_5593_, v_a_5594_, v_a_5595_, v_a_5596_, v_a_5597_, v_a_5598_, v_a_5599_,
    );
    crate::leanh::lean_dec(v_a_5599_);
    crate::leanh::lean_dec_ref(v_a_5598_);
    crate::leanh::lean_dec(v_a_5597_);
    crate::leanh::lean_dec_ref(v_a_5596_);
    crate::leanh::lean_dec(v_a_5595_);
    crate::leanh::lean_dec_ref(v_a_5594_);
    crate::leanh::lean_dec(v_a_5593_);
    return v_res_5601_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5610_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_5611_ = l_Lean_Elab_Term_Quotation_precheckApp___closed__1;
    v___x_5612_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___closed__1;
    v___x_5613_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckApp___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5614_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5610_,
        v___x_5611_,
        v___x_5612_,
        v___x_5613_,
    );
    return v___x_5614_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1___boxed(
    mut v_a_5615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5616_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
    return v_res_5616_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckTypeAscription(
    mut v_x_5629_: *mut crate::leanh::LeanObject,
    mut v_a_5630_: *mut crate::leanh::LeanObject,
    mut v_a_5631_: *mut crate::leanh::LeanObject,
    mut v_a_5632_: *mut crate::leanh::LeanObject,
    mut v_a_5633_: *mut crate::leanh::LeanObject,
    mut v_a_5634_: *mut crate::leanh::LeanObject,
    mut v_a_5635_: *mut crate::leanh::LeanObject,
    mut v_a_5636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5639_: u8 = 0;
    v___x_5638_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1;
    crate::leanh::lean_inc(v_x_5629_);
    v___x_5639_ = l_Lean_Syntax_isOfKind(v_x_5629_, v___x_5638_);
    if v___x_5639_ == 0 {
        let mut v___x_5640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5629_);
        v___x_5640_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_5640_;
    } else {
        let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5644_: u8 = 0;
        v___x_5641_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_5642_ = l_Lean_Syntax_getArg(v_x_5629_, v___x_5641_);
        v___x_5643_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__3;
        crate::leanh::lean_inc(v___x_5642_);
        v___x_5644_ = l_Lean_Syntax_isOfKind(v___x_5642_, v___x_5643_);
        if v___x_5644_ == 0 {
            let mut v___x_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_5642_);
            crate::leanh::lean_dec(v_x_5629_);
            v___x_5645_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
            return v___x_5645_;
        } else {
            let mut v___x_5646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5649_: u8 = 0;
            v___x_5646_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_5647_ = l_Lean_Syntax_getArg(v___x_5642_, v___x_5646_);
            crate::leanh::lean_dec(v___x_5642_);
            v___x_5648_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheck_hasQuotedIdent___closed__1;
            crate::leanh::lean_inc(v___x_5647_);
            v___x_5649_ = l_Lean_Syntax_isOfKind(v___x_5647_, v___x_5648_);
            if v___x_5649_ == 0 {
                let mut v___x_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v___x_5647_);
                crate::leanh::lean_dec(v_x_5629_);
                v___x_5650_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
                return v___x_5650_;
            } else {
                let mut v___x_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_5653_: u8 = 0;
                v___x_5651_ = l_Lean_Syntax_getArg(v___x_5647_, v___x_5641_);
                crate::leanh::lean_dec(v___x_5647_);
                v___x_5652_ = crate::leanh::lean_box(0);
                v___x_5653_ = l_Lean_Syntax_matchesIdent(v___x_5651_, v___x_5652_);
                crate::leanh::lean_dec(v___x_5651_);
                if v___x_5653_ == 0 {
                    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_x_5629_);
                    v___x_5654_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
                    return v___x_5654_;
                } else {
                    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_5658_: u8 = 0;
                    v___x_5655_ = l_Lean_Syntax_getArg(v_x_5629_, v___x_5646_);
                    v___x_5656_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_5657_ = l_Lean_Syntax_getArg(v_x_5629_, v___x_5656_);
                    crate::leanh::lean_dec(v_x_5629_);
                    crate::leanh::lean_inc(v___x_5657_);
                    v___x_5658_ = l_Lean_Syntax_matchesNull(v___x_5657_, v___x_5646_);
                    if v___x_5658_ == 0 {
                        let mut v___x_5659_: u8 = 0;
                        v___x_5659_ = l_Lean_Syntax_matchesNull(v___x_5657_, v___x_5641_);
                        if v___x_5659_ == 0 {
                            let mut v___x_5660_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec(v___x_5655_);
                            v___x_5660_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
                            return v___x_5660_;
                        } else {
                            let mut v___x_5661_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_5661_ = l_Lean_Elab_Term_Quotation_precheck(
                                v___x_5655_,
                                v_a_5630_,
                                v_a_5631_,
                                v_a_5632_,
                                v_a_5633_,
                                v_a_5634_,
                                v_a_5635_,
                                v_a_5636_,
                            );
                            return v___x_5661_;
                        }
                    } else {
                        let mut v___x_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_5662_ = l_Lean_Elab_Term_Quotation_precheck(
                            v___x_5655_,
                            v_a_5630_,
                            v_a_5631_,
                            v_a_5632_,
                            v_a_5633_,
                            v_a_5634_,
                            v_a_5635_,
                            v_a_5636_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5662_) == 0 {
                            let mut v___x_5663_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_5664_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref_known(v___x_5662_, 1);
                            v___x_5663_ = l_Lean_Syntax_getArg(v___x_5657_, v___x_5641_);
                            crate::leanh::lean_dec(v___x_5657_);
                            v___x_5664_ = l_Lean_Elab_Term_Quotation_precheck(
                                v___x_5663_,
                                v_a_5630_,
                                v_a_5631_,
                                v_a_5632_,
                                v_a_5633_,
                                v_a_5634_,
                                v_a_5635_,
                                v_a_5636_,
                            );
                            return v___x_5664_;
                        } else {
                            crate::leanh::lean_dec(v___x_5657_);
                            return v___x_5662_;
                        }
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed(
    mut v_x_5665_: *mut crate::leanh::LeanObject,
    mut v_a_5666_: *mut crate::leanh::LeanObject,
    mut v_a_5667_: *mut crate::leanh::LeanObject,
    mut v_a_5668_: *mut crate::leanh::LeanObject,
    mut v_a_5669_: *mut crate::leanh::LeanObject,
    mut v_a_5670_: *mut crate::leanh::LeanObject,
    mut v_a_5671_: *mut crate::leanh::LeanObject,
    mut v_a_5672_: *mut crate::leanh::LeanObject,
    mut v_a_5673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5674_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription(
        v_x_5665_, v_a_5666_, v_a_5667_, v_a_5668_, v_a_5669_, v_a_5670_, v_a_5671_, v_a_5672_,
    );
    crate::leanh::lean_dec(v_a_5672_);
    crate::leanh::lean_dec_ref(v_a_5671_);
    crate::leanh::lean_dec(v_a_5670_);
    crate::leanh::lean_dec_ref(v_a_5669_);
    crate::leanh::lean_dec(v_a_5668_);
    crate::leanh::lean_dec_ref(v_a_5667_);
    crate::leanh::lean_dec(v_a_5666_);
    return v_res_5674_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5683_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_5684_ = l_Lean_Elab_Term_Quotation_precheckTypeAscription___closed__1;
    v___x_5685_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___closed__1;
    v___x_5686_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckTypeAscription___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5687_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5683_,
        v___x_5684_,
        v___x_5685_,
        v___x_5686_,
    );
    return v___x_5687_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1___boxed(
    mut v_a_5688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5689_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
    return v_res_5689_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckExplicit(
    mut v_x_5696_: *mut crate::leanh::LeanObject,
    mut v_a_5697_: *mut crate::leanh::LeanObject,
    mut v_a_5698_: *mut crate::leanh::LeanObject,
    mut v_a_5699_: *mut crate::leanh::LeanObject,
    mut v_a_5700_: *mut crate::leanh::LeanObject,
    mut v_a_5701_: *mut crate::leanh::LeanObject,
    mut v_a_5702_: *mut crate::leanh::LeanObject,
    mut v_a_5703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: u8 = 0;
    v___x_5705_ = l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1;
    crate::leanh::lean_inc(v_x_5696_);
    v___x_5706_ = l_Lean_Syntax_isOfKind(v_x_5696_, v___x_5705_);
    if v___x_5706_ == 0 {
        let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_5696_);
        v___x_5707_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_5707_;
    } else {
        let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_5708_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_5709_ = l_Lean_Syntax_getArg(v_x_5696_, v___x_5708_);
        crate::leanh::lean_dec(v_x_5696_);
        v___x_5710_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_5709_,
            v_a_5697_,
            v_a_5698_,
            v_a_5699_,
            v_a_5700_,
            v_a_5701_,
            v_a_5702_,
            v_a_5703_,
        );
        return v___x_5710_;
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckExplicit___boxed(
    mut v_x_5711_: *mut crate::leanh::LeanObject,
    mut v_a_5712_: *mut crate::leanh::LeanObject,
    mut v_a_5713_: *mut crate::leanh::LeanObject,
    mut v_a_5714_: *mut crate::leanh::LeanObject,
    mut v_a_5715_: *mut crate::leanh::LeanObject,
    mut v_a_5716_: *mut crate::leanh::LeanObject,
    mut v_a_5717_: *mut crate::leanh::LeanObject,
    mut v_a_5718_: *mut crate::leanh::LeanObject,
    mut v_a_5719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l_Lean_Elab_Term_Quotation_precheckExplicit(
        v_x_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_, v_a_5718_,
    );
    crate::leanh::lean_dec(v_a_5718_);
    crate::leanh::lean_dec_ref(v_a_5717_);
    crate::leanh::lean_dec(v_a_5716_);
    crate::leanh::lean_dec_ref(v_a_5715_);
    crate::leanh::lean_dec(v_a_5714_);
    crate::leanh::lean_dec_ref(v_a_5713_);
    crate::leanh::lean_dec(v_a_5712_);
    return v_res_5720_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5729_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_5730_ = l_Lean_Elab_Term_Quotation_precheckExplicit___closed__1;
    v___x_5731_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___closed__1;
    v___x_5732_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckExplicit___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5733_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5729_,
        v___x_5730_,
        v___x_5731_,
        v___x_5732_,
    );
    return v___x_5733_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1___boxed(
    mut v_a_5734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5735_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
    return v_res_5735_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__0;
    v___x_5738_ = l_Lean_stringToMessageData(v___x_5737_);
    return v___x_5738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(
    mut v_as_5739_: *mut crate::leanh::LeanObject,
    mut v_i_5740_: usize,
    mut v_stop_5741_: usize,
    mut v_b_5742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: usize = 0;
    let mut v___x_5746_: usize = 0;
    let mut v___x_5748_: u8 = 0;
    let mut v___x_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5754_: u8 = 0;
    let mut v_a_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5764_: u8 = 0;
    let mut v_unused_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5748_ = lean_usize_dec_eq(v_i_5740_, v_stop_5741_);
                if v___x_5748_ == 0 {
                    v___x_5749_ = lean_array_uget(v_as_5739_, v_i_5740_);
                    v_fst_5750_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                    crate::leanh::lean_inc(v_fst_5750_);
                    if crate::leanh::lean_obj_tag(v_fst_5750_) == 0 {
                        v_snd_5751_ = crate::leanh::lean_ctor_get(v___x_5749_, 1);
                        v_isSharedCheck_5764_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5749_)) as u8;
                        if v_isSharedCheck_5764_ == 0 {
                            v_unused_5765_ = crate::leanh::lean_ctor_get(v___x_5749_, 0);
                            crate::leanh::lean_dec(v_unused_5765_);
                            v___x_5753_ = v___x_5749_;
                            v_isShared_5754_ = v_isSharedCheck_5764_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_5751_);
                            crate::leanh::lean_dec(v___x_5749_);
                            v___x_5753_ = crate::leanh::lean_box(0);
                            v_isShared_5754_ = v_isSharedCheck_5764_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_5750_);
                        crate::leanh::lean_dec(v___x_5749_);
                        v___y_5744_ = v_b_5742_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5742_;
                }
            }
            1 => {
                v___x_5745_ = 1usize;
                v___x_5746_ = lean_usize_add(v_i_5740_, v___x_5745_);
                v_i_5740_ = v___x_5746_;
                v_b_5742_ = v___y_5744_;
                state = 0;
                continue;
            }
            2 => {
                v_a_5755_ = crate::leanh::lean_ctor_get(v_fst_5750_, 0);
                crate::leanh::lean_inc(v_a_5755_);
                crate::leanh::lean_dec_ref_known(v_fst_5750_, 1);
                v___x_5756_ = l_Lean_MessageData_ofSyntax(v_snd_5751_);
                v___x_5757_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___closed__1);
                if v_isShared_5754_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5753_, 7);
                    crate::leanh::lean_ctor_set(v___x_5753_, 1, v___x_5757_);
                    crate::leanh::lean_ctor_set(v___x_5753_, 0, v___x_5756_);
                    v___x_5759_ = v___x_5753_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5763_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 0, v___x_5756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5763_, 1, v___x_5757_);
                    v___x_5759_ = v_reuseFailAlloc_5763_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5760_ = l_Lean_Exception_toMessageData(v_a_5755_);
                v___x_5761_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5761_, 0, v___x_5759_);
                crate::leanh::lean_ctor_set(v___x_5761_, 1, v___x_5760_);
                v___x_5762_ = lean_array_push(v_b_5742_, v___x_5761_);
                v___y_5744_ = v___x_5762_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1___boxed(
    mut v_as_5766_: *mut crate::leanh::LeanObject,
    mut v_i_5767_: *mut crate::leanh::LeanObject,
    mut v_stop_5768_: *mut crate::leanh::LeanObject,
    mut v_b_5769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5770_: usize = 0;
    let mut v_stop_boxed_5771_: usize = 0;
    let mut v_res_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5770_ = crate::leanh::lean_unbox_usize(v_i_5767_);
    crate::leanh::lean_dec(v_i_5767_);
    v_stop_boxed_5771_ = crate::leanh::lean_unbox_usize(v_stop_5768_);
    crate::leanh::lean_dec(v_stop_5768_);
    v_res_5772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_5766_, v_i_boxed_5770_, v_stop_boxed_5771_, v_b_5769_);
    crate::leanh::lean_dec_ref(v_as_5766_);
    return v_res_5772_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(
    mut v_as_5773_: *mut crate::leanh::LeanObject,
    mut v_start_5774_: *mut crate::leanh::LeanObject,
    mut v_stop_5775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: u8 = 0;
    v___x_5776_ = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__0___redArg___closed__1;
    v___x_5777_ = lean_nat_dec_lt(v_start_5774_, v_stop_5775_);
    if v___x_5777_ == 0 {
        return v___x_5776_;
    } else {
        let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5779_: u8 = 0;
        v___x_5778_ = lean_array_get_size(v_as_5773_);
        v___x_5779_ = lean_nat_dec_le(v_stop_5775_, v___x_5778_);
        if v___x_5779_ == 0 {
            let mut v___x_5780_: u8 = 0;
            v___x_5780_ = lean_nat_dec_lt(v_start_5774_, v___x_5778_);
            if v___x_5780_ == 0 {
                return v___x_5776_;
            } else {
                let mut v___x_5781_: usize = 0;
                let mut v___x_5782_: usize = 0;
                let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_5781_ = lean_usize_of_nat(v_start_5774_);
                v___x_5782_ = lean_usize_of_nat(v___x_5778_);
                v___x_5783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_5773_, v___x_5781_, v___x_5782_, v___x_5776_);
                return v___x_5783_;
            }
        } else {
            let mut v___x_5784_: usize = 0;
            let mut v___x_5785_: usize = 0;
            let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_5784_ = lean_usize_of_nat(v_start_5774_);
            v___x_5785_ = lean_usize_of_nat(v_stop_5775_);
            v___x_5786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1_spec__1(v_as_5773_, v___x_5784_, v___x_5785_, v___x_5776_);
            return v___x_5786_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1___boxed(
    mut v_as_5787_: *mut crate::leanh::LeanObject,
    mut v_start_5788_: *mut crate::leanh::LeanObject,
    mut v_stop_5789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5790_ = l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(
        v_as_5787_,
        v_start_5788_,
        v_stop_5789_,
    );
    crate::leanh::lean_dec(v_stop_5789_);
    crate::leanh::lean_dec(v_start_5788_);
    crate::leanh::lean_dec_ref(v_as_5787_);
    return v_res_5790_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(
    mut v_sz_5791_: usize,
    mut v_i_5792_: usize,
    mut v_bs_5793_: *mut crate::leanh::LeanObject,
    mut v___y_5794_: *mut crate::leanh::LeanObject,
    mut v___y_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
    mut v___y_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
    mut v___y_5800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5802_: u8 = 0;
    let mut v___x_5803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: usize = 0;
    let mut v___x_5810_: usize = 0;
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___y_5821_: u8 = 0;
    let mut v___x_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: u8 = 0;
    let mut v___x_5827_: u8 = 0;
    let mut v_isSharedCheck_5828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5802_ = lean_usize_dec_lt(v_i_5792_, v_sz_5791_);
                if v___x_5802_ == 0 {
                    v___x_5803_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5803_, 0, v_bs_5793_);
                    return v___x_5803_;
                } else {
                    v_v_5804_ = lean_array_uget(v_bs_5793_, v_i_5792_);
                    v___x_5805_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5806_ = lean_array_uset(v_bs_5793_, v_i_5792_, v___x_5805_);
                    v___x_5813_ = l_Lean_Elab_Term_Quotation_precheck(
                        v_v_5804_,
                        v___y_5794_,
                        v___y_5795_,
                        v___y_5796_,
                        v___y_5797_,
                        v___y_5798_,
                        v___y_5799_,
                        v___y_5800_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5813_) == 0 {
                        v_a_5814_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                        crate::leanh::lean_inc(v_a_5814_);
                        crate::leanh::lean_dec_ref_known(v___x_5813_, 1);
                        v___x_5815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5815_, 0, v_a_5814_);
                        v_a_5808_ = v___x_5815_;
                        state = 1;
                        continue;
                    } else {
                        v_a_5816_ = crate::leanh::lean_ctor_get(v___x_5813_, 0);
                        v_isSharedCheck_5828_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5813_)) as u8;
                        if v_isSharedCheck_5828_ == 0 {
                            v___x_5818_ = v___x_5813_;
                            v_isShared_5819_ = v_isSharedCheck_5828_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5816_);
                            crate::leanh::lean_dec(v___x_5813_);
                            v___x_5818_ = crate::leanh::lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5828_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5809_ = 1usize;
                v___x_5810_ = lean_usize_add(v_i_5792_, v___x_5809_);
                v___x_5811_ = lean_array_uset(v_bs_x27_5806_, v_i_5792_, v_a_5808_);
                v_i_5792_ = v___x_5810_;
                v_bs_5793_ = v___x_5811_;
                state = 0;
                continue;
            }
            2 => {
                v___x_5826_ = l_Lean_Exception_isInterrupt(v_a_5816_);
                if v___x_5826_ == 0 {
                    crate::leanh::lean_inc(v_a_5816_);
                    v___x_5827_ = l_Lean_Exception_isRuntime(v_a_5816_);
                    v___y_5821_ = v___x_5827_;
                    state = 3;
                    continue;
                } else {
                    v___y_5821_ = v___x_5826_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_5821_ == 0 {
                    crate::leanh::lean_del_object(v___x_5818_);
                    v___x_5822_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5822_, 0, v_a_5816_);
                    v_a_5808_ = v___x_5822_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_bs_x27_5806_);
                    if v_isShared_5819_ == 0 {
                        v___x_5824_ = v___x_5818_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5825_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_a_5816_);
                        v___x_5824_ = v_reuseFailAlloc_5825_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5824_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0___boxed(
    mut v_sz_5829_: *mut crate::leanh::LeanObject,
    mut v_i_5830_: *mut crate::leanh::LeanObject,
    mut v_bs_5831_: *mut crate::leanh::LeanObject,
    mut v___y_5832_: *mut crate::leanh::LeanObject,
    mut v___y_5833_: *mut crate::leanh::LeanObject,
    mut v___y_5834_: *mut crate::leanh::LeanObject,
    mut v___y_5835_: *mut crate::leanh::LeanObject,
    mut v___y_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5840_: usize = 0;
    let mut v_i_boxed_5841_: usize = 0;
    let mut v_res_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5840_ = crate::leanh::lean_unbox_usize(v_sz_5829_);
    crate::leanh::lean_dec(v_sz_5829_);
    v_i_boxed_5841_ = crate::leanh::lean_unbox_usize(v_i_5830_);
    crate::leanh::lean_dec(v_i_5830_);
    v_res_5842_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_boxed_5840_, v_i_boxed_5841_, v_bs_5831_, v___y_5832_, v___y_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_, v___y_5838_);
    crate::leanh::lean_dec(v___y_5838_);
    crate::leanh::lean_dec_ref(v___y_5837_);
    crate::leanh::lean_dec(v___y_5836_);
    crate::leanh::lean_dec_ref(v___y_5835_);
    crate::leanh::lean_dec(v___y_5834_);
    crate::leanh::lean_dec_ref(v___y_5833_);
    crate::leanh::lean_dec(v___y_5832_);
    return v_res_5842_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5844_ = l_Lean_Elab_Term_Quotation_precheckChoice___closed__0;
    v___x_5845_ = l_Lean_stringToMessageData(v___x_5844_);
    return v___x_5845_;
}
pub unsafe fn _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5847_ = l_Lean_Elab_Term_Quotation_precheckChoice___closed__2;
    v___x_5848_ = l_Lean_stringToMessageData(v___x_5847_);
    return v___x_5848_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckChoice(
    mut v_stx_5849_: *mut crate::leanh::LeanObject,
    mut v_a_5850_: *mut crate::leanh::LeanObject,
    mut v_a_5851_: *mut crate::leanh::LeanObject,
    mut v_a_5852_: *mut crate::leanh::LeanObject,
    mut v_a_5853_: *mut crate::leanh::LeanObject,
    mut v_a_5854_: *mut crate::leanh::LeanObject,
    mut v_a_5855_: *mut crate::leanh::LeanObject,
    mut v_a_5856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5859_: usize = 0;
    let mut v___x_5860_: usize = 0;
    let mut v___x_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5865_: u8 = 0;
    let mut v___x_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: u8 = 0;
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5883_: u8 = 0;
    let mut v_a_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v___x_5889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5858_ = l_Lean_Syntax_getArgs(v_stx_5849_);
                v_sz_5859_ = lean_array_size(v___x_5858_);
                v___x_5860_ = 0usize;
                crate::leanh::lean_inc_ref(v___x_5858_);
                v___x_5861_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__0(v_sz_5859_, v___x_5860_, v___x_5858_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_);
                if crate::leanh::lean_obj_tag(v___x_5861_) == 0 {
                    v_a_5862_ = crate::leanh::lean_ctor_get(v___x_5861_, 0);
                    v_isSharedCheck_5883_ = (!crate::leanh::lean_is_exclusive(v___x_5861_)) as u8;
                    if v_isSharedCheck_5883_ == 0 {
                        v___x_5864_ = v___x_5861_;
                        v_isShared_5865_ = v_isSharedCheck_5883_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5862_);
                        crate::leanh::lean_dec(v___x_5861_);
                        v___x_5864_ = crate::leanh::lean_box(0);
                        v_isShared_5865_ = v_isSharedCheck_5883_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_5858_);
                    v_a_5884_ = crate::leanh::lean_ctor_get(v___x_5861_, 0);
                    v_isSharedCheck_5891_ = (!crate::leanh::lean_is_exclusive(v___x_5861_)) as u8;
                    if v_isSharedCheck_5891_ == 0 {
                        v___x_5886_ = v___x_5861_;
                        v_isShared_5887_ = v_isSharedCheck_5891_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5884_);
                        crate::leanh::lean_dec(v___x_5861_);
                        v___x_5886_ = crate::leanh::lean_box(0);
                        v_isShared_5887_ = v_isSharedCheck_5891_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5866_ = l_Array_zip___redArg(v_a_5862_, v___x_5858_);
                crate::leanh::lean_dec_ref(v___x_5858_);
                crate::leanh::lean_dec(v_a_5862_);
                v___x_5867_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5868_ = lean_array_get_size(v___x_5866_);
                v___x_5869_ =
                    l_Array_filterMapM___at___00Lean_Elab_Term_Quotation_precheckChoice_spec__1(
                        v___x_5866_,
                        v___x_5867_,
                        v___x_5868_,
                    );
                crate::leanh::lean_dec_ref(v___x_5866_);
                v___x_5870_ = lean_array_get_size(v___x_5869_);
                v___x_5871_ = lean_nat_dec_eq(v___x_5870_, v___x_5867_);
                if v___x_5871_ == 0 {
                    crate::leanh::lean_del_object(v___x_5864_);
                    v___x_5872_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Quotation_precheckChoice___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Quotation_precheckChoice___closed__1_once
                        ),
                        _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__1,
                    );
                    v___x_5873_ = lean_array_to_list(v___x_5869_);
                    v___x_5874_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Quotation_precheckChoice___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Term_Quotation_precheckChoice___closed__3_once
                        ),
                        _init_l_Lean_Elab_Term_Quotation_precheckChoice___closed__3,
                    );
                    v___x_5875_ = l_Lean_MessageData_joinSep(v___x_5873_, v___x_5874_);
                    v___x_5876_ = l_Lean_indentD(v___x_5875_);
                    v___x_5877_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5877_, 0, v___x_5872_);
                    crate::leanh::lean_ctor_set(v___x_5877_, 1, v___x_5876_);
                    v___x_5878_ = l_Lean_throwErrorAt___at___00Lean_Elab_Term_Quotation_precheck_spec__1___redArg(v_stx_5849_, v___x_5877_, v_a_5850_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_);
                    return v___x_5878_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5869_);
                    v___x_5879_ = crate::leanh::lean_box(0);
                    if v_isShared_5865_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5864_, 0, v___x_5879_);
                        v___x_5881_ = v___x_5864_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5882_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5882_, 0, v___x_5879_);
                        v___x_5881_ = v_reuseFailAlloc_5882_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5881_;
            }
            3 => {
                if v_isShared_5887_ == 0 {
                    v___x_5889_ = v___x_5886_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5890_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
                    v___x_5889_ = v_reuseFailAlloc_5890_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckChoice___boxed(
    mut v_stx_5892_: *mut crate::leanh::LeanObject,
    mut v_a_5893_: *mut crate::leanh::LeanObject,
    mut v_a_5894_: *mut crate::leanh::LeanObject,
    mut v_a_5895_: *mut crate::leanh::LeanObject,
    mut v_a_5896_: *mut crate::leanh::LeanObject,
    mut v_a_5897_: *mut crate::leanh::LeanObject,
    mut v_a_5898_: *mut crate::leanh::LeanObject,
    mut v_a_5899_: *mut crate::leanh::LeanObject,
    mut v_a_5900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5901_ = l_Lean_Elab_Term_Quotation_precheckChoice(
        v_stx_5892_,
        v_a_5893_,
        v_a_5894_,
        v_a_5895_,
        v_a_5896_,
        v_a_5897_,
        v_a_5898_,
        v_a_5899_,
    );
    crate::leanh::lean_dec(v_a_5899_);
    crate::leanh::lean_dec_ref(v_a_5898_);
    crate::leanh::lean_dec(v_a_5897_);
    crate::leanh::lean_dec_ref(v_a_5896_);
    crate::leanh::lean_dec(v_a_5895_);
    crate::leanh::lean_dec_ref(v_a_5894_);
    crate::leanh::lean_dec(v_a_5893_);
    crate::leanh::lean_dec(v_stx_5892_);
    return v_res_5901_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5913_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_5914_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__1;
    v___x_5915_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___closed__3;
    v___x_5916_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckChoice___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5917_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5913_,
        v___x_5914_,
        v___x_5915_,
        v___x_5916_,
    );
    return v___x_5917_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1___boxed(
    mut v_a_5918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5919_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
    return v_res_5919_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(
    mut v_singleQuot_5920_: *mut crate::leanh::LeanObject,
    mut v_x_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
    mut v___y_5923_: *mut crate::leanh::LeanObject,
    mut v___y_5924_: *mut crate::leanh::LeanObject,
    mut v___y_5925_: *mut crate::leanh::LeanObject,
    mut v___y_5926_: *mut crate::leanh::LeanObject,
    mut v___y_5927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5929_, 0, v_singleQuot_5920_);
    return v___x_5929_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed(
    mut v_singleQuot_5930_: *mut crate::leanh::LeanObject,
    mut v_x_5931_: *mut crate::leanh::LeanObject,
    mut v___y_5932_: *mut crate::leanh::LeanObject,
    mut v___y_5933_: *mut crate::leanh::LeanObject,
    mut v___y_5934_: *mut crate::leanh::LeanObject,
    mut v___y_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
    mut v___y_5937_: *mut crate::leanh::LeanObject,
    mut v___y_5938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5939_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0(
        v_singleQuot_5930_,
        v_x_5931_,
        v___y_5932_,
        v___y_5933_,
        v___y_5934_,
        v___y_5935_,
        v___y_5936_,
        v___y_5937_,
    );
    crate::leanh::lean_dec(v___y_5937_);
    crate::leanh::lean_dec_ref(v___y_5936_);
    crate::leanh::lean_dec(v___y_5935_);
    crate::leanh::lean_dec_ref(v___y_5934_);
    crate::leanh::lean_dec(v___y_5933_);
    crate::leanh::lean_dec_ref(v___y_5932_);
    crate::leanh::lean_dec(v_x_5931_);
    return v_res_5939_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(
    mut v_stx_5940_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_5941_: *mut crate::leanh::LeanObject,
    mut v_a_5942_: *mut crate::leanh::LeanObject,
    mut v_a_5943_: *mut crate::leanh::LeanObject,
    mut v_a_5944_: *mut crate::leanh::LeanObject,
    mut v_a_5945_: *mut crate::leanh::LeanObject,
    mut v_a_5946_: *mut crate::leanh::LeanObject,
    mut v_a_5947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_singleQuot_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5949_ = crate::leanh::lean_unsigned_to_nat(1);
                v_singleQuot_5950_ = l_Lean_Syntax_getArg(v_stx_5940_, v___x_5949_);
                crate::leanh::lean_inc(v_singleQuot_5950_);
                v___x_5951_ = l_Lean_Syntax_getQuotContent(v_singleQuot_5950_);
                v___x_5952_ = l_Lean_Elab_Term_Quotation_runPrecheck(
                    v___x_5951_,
                    v_a_5942_,
                    v_a_5943_,
                    v_a_5944_,
                    v_a_5945_,
                    v_a_5946_,
                    v_a_5947_,
                );
                if crate::leanh::lean_obj_tag(v___x_5952_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5952_, 1);
                    v___f_5953_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___lam__0___boxed
                            as *mut core::ffi::c_void,
                        9,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5953_, 0, v_singleQuot_5950_);
                    v___x_5954_ = l_Lean_Elab_Term_adaptExpander(
                        v___f_5953_,
                        v_stx_5940_,
                        v_expectedType_x3f_5941_,
                        v_a_5942_,
                        v_a_5943_,
                        v_a_5944_,
                        v_a_5945_,
                        v_a_5946_,
                        v_a_5947_,
                    );
                    return v___x_5954_;
                } else {
                    crate::leanh::lean_dec(v_singleQuot_5950_);
                    crate::leanh::lean_dec(v_expectedType_x3f_5941_);
                    crate::leanh::lean_dec(v_stx_5940_);
                    v_a_5955_ = crate::leanh::lean_ctor_get(v___x_5952_, 0);
                    v_isSharedCheck_5962_ = (!crate::leanh::lean_is_exclusive(v___x_5952_)) as u8;
                    if v_isSharedCheck_5962_ == 0 {
                        v___x_5957_ = v___x_5952_;
                        v_isShared_5958_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5955_);
                        crate::leanh::lean_dec(v___x_5952_);
                        v___x_5957_ = crate::leanh::lean_box(0);
                        v_isShared_5958_ = v_isSharedCheck_5962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5958_ == 0 {
                    v___x_5960_ = v___x_5957_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_a_5955_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed(
    mut v_stx_5963_: *mut crate::leanh::LeanObject,
    mut v_expectedType_x3f_5964_: *mut crate::leanh::LeanObject,
    mut v_a_5965_: *mut crate::leanh::LeanObject,
    mut v_a_5966_: *mut crate::leanh::LeanObject,
    mut v_a_5967_: *mut crate::leanh::LeanObject,
    mut v_a_5968_: *mut crate::leanh::LeanObject,
    mut v_a_5969_: *mut crate::leanh::LeanObject,
    mut v_a_5970_: *mut crate::leanh::LeanObject,
    mut v_a_5971_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5972_ = l_Lean_Elab_Term_Quotation_elabPrecheckedQuot(
        v_stx_5963_,
        v_expectedType_x3f_5964_,
        v_a_5965_,
        v_a_5966_,
        v_a_5967_,
        v_a_5968_,
        v_a_5969_,
        v_a_5970_,
    );
    crate::leanh::lean_dec(v_a_5970_);
    crate::leanh::lean_dec_ref(v_a_5969_);
    crate::leanh::lean_dec(v_a_5968_);
    crate::leanh::lean_dec_ref(v_a_5967_);
    crate::leanh::lean_dec(v_a_5966_);
    crate::leanh::lean_dec_ref(v_a_5965_);
    return v_res_5972_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5987_ = l_Lean_Elab_Term_termElabAttribute;
    v___x_5988_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__1;
    v___x_5989_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3;
    v___x_5990_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_elabPrecheckedQuot___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_5991_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_5987_,
        v___x_5988_,
        v___x_5989_,
        v___x_5990_,
    );
    return v___x_5991_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___boxed(
    mut v_a_5992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5993_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
    return v_res_5993_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6020_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1___closed__3;
    v___x_6021_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___closed__6;
    v___x_6022_ = l_Lean_addBuiltinDeclarationRanges(v___x_6020_, v___x_6021_);
    return v___x_6022_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3___boxed(
    mut v_a_6023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6024_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
    return v_res_6024_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinrel(
    mut v_x_6031_: *mut crate::leanh::LeanObject,
    mut v_a_6032_: *mut crate::leanh::LeanObject,
    mut v_a_6033_: *mut crate::leanh::LeanObject,
    mut v_a_6034_: *mut crate::leanh::LeanObject,
    mut v_a_6035_: *mut crate::leanh::LeanObject,
    mut v_a_6036_: *mut crate::leanh::LeanObject,
    mut v_a_6037_: *mut crate::leanh::LeanObject,
    mut v_a_6038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: u8 = 0;
    v___x_6040_ = l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1;
    crate::leanh::lean_inc(v_x_6031_);
    v___x_6041_ = l_Lean_Syntax_isOfKind(v_x_6031_, v___x_6040_);
    if v___x_6041_ == 0 {
        let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6031_);
        v___x_6042_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6042_;
    } else {
        let mut v___x_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6043_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6044_ = l_Lean_Syntax_getArg(v_x_6031_, v___x_6043_);
        v___x_6045_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6044_,
            v_a_6032_,
            v_a_6033_,
            v_a_6034_,
            v_a_6035_,
            v_a_6036_,
            v_a_6037_,
            v_a_6038_,
        );
        if crate::leanh::lean_obj_tag(v___x_6045_) == 0 {
            let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6045_, 1);
            v___x_6046_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6047_ = l_Lean_Syntax_getArg(v_x_6031_, v___x_6046_);
            v___x_6048_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6047_,
                v_a_6032_,
                v_a_6033_,
                v_a_6034_,
                v_a_6035_,
                v_a_6036_,
                v_a_6037_,
                v_a_6038_,
            );
            if crate::leanh::lean_obj_tag(v___x_6048_) == 0 {
                let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_6048_, 1);
                v___x_6049_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6050_ = l_Lean_Syntax_getArg(v_x_6031_, v___x_6049_);
                crate::leanh::lean_dec(v_x_6031_);
                v___x_6051_ = l_Lean_Elab_Term_Quotation_precheck(
                    v___x_6050_,
                    v_a_6032_,
                    v_a_6033_,
                    v_a_6034_,
                    v_a_6035_,
                    v_a_6036_,
                    v_a_6037_,
                    v_a_6038_,
                );
                return v___x_6051_;
            } else {
                crate::leanh::lean_dec(v_x_6031_);
                return v___x_6048_;
            }
        } else {
            crate::leanh::lean_dec(v_x_6031_);
            return v___x_6045_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinrel___boxed(
    mut v_x_6052_: *mut crate::leanh::LeanObject,
    mut v_a_6053_: *mut crate::leanh::LeanObject,
    mut v_a_6054_: *mut crate::leanh::LeanObject,
    mut v_a_6055_: *mut crate::leanh::LeanObject,
    mut v_a_6056_: *mut crate::leanh::LeanObject,
    mut v_a_6057_: *mut crate::leanh::LeanObject,
    mut v_a_6058_: *mut crate::leanh::LeanObject,
    mut v_a_6059_: *mut crate::leanh::LeanObject,
    mut v_a_6060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6061_ = l_Lean_Elab_Term_Quotation_precheckBinrel(
        v_x_6052_, v_a_6053_, v_a_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_, v_a_6059_,
    );
    crate::leanh::lean_dec(v_a_6059_);
    crate::leanh::lean_dec_ref(v_a_6058_);
    crate::leanh::lean_dec(v_a_6057_);
    crate::leanh::lean_dec_ref(v_a_6056_);
    crate::leanh::lean_dec(v_a_6055_);
    crate::leanh::lean_dec_ref(v_a_6054_);
    crate::leanh::lean_dec(v_a_6053_);
    return v_res_6061_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6070_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6071_ = l_Lean_Elab_Term_Quotation_precheckBinrel___closed__1;
    v___x_6072_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___closed__1;
    v___x_6073_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckBinrel___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6074_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6070_,
        v___x_6071_,
        v___x_6072_,
        v___x_6073_,
    );
    return v___x_6074_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1___boxed(
    mut v_a_6075_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6076_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
    return v_res_6076_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(
    mut v_x_6083_: *mut crate::leanh::LeanObject,
    mut v_a_6084_: *mut crate::leanh::LeanObject,
    mut v_a_6085_: *mut crate::leanh::LeanObject,
    mut v_a_6086_: *mut crate::leanh::LeanObject,
    mut v_a_6087_: *mut crate::leanh::LeanObject,
    mut v_a_6088_: *mut crate::leanh::LeanObject,
    mut v_a_6089_: *mut crate::leanh::LeanObject,
    mut v_a_6090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: u8 = 0;
    v___x_6092_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1;
    crate::leanh::lean_inc(v_x_6083_);
    v___x_6093_ = l_Lean_Syntax_isOfKind(v_x_6083_, v___x_6092_);
    if v___x_6093_ == 0 {
        let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6083_);
        v___x_6094_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6094_;
    } else {
        let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6095_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6096_ = l_Lean_Syntax_getArg(v_x_6083_, v___x_6095_);
        v___x_6097_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6096_,
            v_a_6084_,
            v_a_6085_,
            v_a_6086_,
            v_a_6087_,
            v_a_6088_,
            v_a_6089_,
            v_a_6090_,
        );
        if crate::leanh::lean_obj_tag(v___x_6097_) == 0 {
            let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6097_, 1);
            v___x_6098_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6099_ = l_Lean_Syntax_getArg(v_x_6083_, v___x_6098_);
            v___x_6100_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6099_,
                v_a_6084_,
                v_a_6085_,
                v_a_6086_,
                v_a_6087_,
                v_a_6088_,
                v_a_6089_,
                v_a_6090_,
            );
            if crate::leanh::lean_obj_tag(v___x_6100_) == 0 {
                let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_6100_, 1);
                v___x_6101_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6102_ = l_Lean_Syntax_getArg(v_x_6083_, v___x_6101_);
                crate::leanh::lean_dec(v_x_6083_);
                v___x_6103_ = l_Lean_Elab_Term_Quotation_precheck(
                    v___x_6102_,
                    v_a_6084_,
                    v_a_6085_,
                    v_a_6086_,
                    v_a_6087_,
                    v_a_6088_,
                    v_a_6089_,
                    v_a_6090_,
                );
                return v___x_6103_;
            } else {
                crate::leanh::lean_dec(v_x_6083_);
                return v___x_6100_;
            }
        } else {
            crate::leanh::lean_dec(v_x_6083_);
            return v___x_6097_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed(
    mut v_x_6104_: *mut crate::leanh::LeanObject,
    mut v_a_6105_: *mut crate::leanh::LeanObject,
    mut v_a_6106_: *mut crate::leanh::LeanObject,
    mut v_a_6107_: *mut crate::leanh::LeanObject,
    mut v_a_6108_: *mut crate::leanh::LeanObject,
    mut v_a_6109_: *mut crate::leanh::LeanObject,
    mut v_a_6110_: *mut crate::leanh::LeanObject,
    mut v_a_6111_: *mut crate::leanh::LeanObject,
    mut v_a_6112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6113_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp(
        v_x_6104_, v_a_6105_, v_a_6106_, v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_, v_a_6111_,
    );
    crate::leanh::lean_dec(v_a_6111_);
    crate::leanh::lean_dec_ref(v_a_6110_);
    crate::leanh::lean_dec(v_a_6109_);
    crate::leanh::lean_dec_ref(v_a_6108_);
    crate::leanh::lean_dec(v_a_6107_);
    crate::leanh::lean_dec_ref(v_a_6106_);
    crate::leanh::lean_dec(v_a_6105_);
    return v_res_6113_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6122_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6123_ = l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___closed__1;
    v___x_6124_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___closed__1;
    v___x_6125_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckBinrelNoProp___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6126_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6122_,
        v___x_6123_,
        v___x_6124_,
        v___x_6125_,
    );
    return v___x_6126_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1___boxed(
    mut v_a_6127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6128_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
    return v_res_6128_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinop(
    mut v_x_6135_: *mut crate::leanh::LeanObject,
    mut v_a_6136_: *mut crate::leanh::LeanObject,
    mut v_a_6137_: *mut crate::leanh::LeanObject,
    mut v_a_6138_: *mut crate::leanh::LeanObject,
    mut v_a_6139_: *mut crate::leanh::LeanObject,
    mut v_a_6140_: *mut crate::leanh::LeanObject,
    mut v_a_6141_: *mut crate::leanh::LeanObject,
    mut v_a_6142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: u8 = 0;
    v___x_6144_ = l_Lean_Elab_Term_Quotation_precheckBinop___closed__1;
    crate::leanh::lean_inc(v_x_6135_);
    v___x_6145_ = l_Lean_Syntax_isOfKind(v_x_6135_, v___x_6144_);
    if v___x_6145_ == 0 {
        let mut v___x_6146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6135_);
        v___x_6146_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6146_;
    } else {
        let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6147_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6148_ = l_Lean_Syntax_getArg(v_x_6135_, v___x_6147_);
        v___x_6149_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6148_,
            v_a_6136_,
            v_a_6137_,
            v_a_6138_,
            v_a_6139_,
            v_a_6140_,
            v_a_6141_,
            v_a_6142_,
        );
        if crate::leanh::lean_obj_tag(v___x_6149_) == 0 {
            let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6149_, 1);
            v___x_6150_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6151_ = l_Lean_Syntax_getArg(v_x_6135_, v___x_6150_);
            v___x_6152_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6151_,
                v_a_6136_,
                v_a_6137_,
                v_a_6138_,
                v_a_6139_,
                v_a_6140_,
                v_a_6141_,
                v_a_6142_,
            );
            if crate::leanh::lean_obj_tag(v___x_6152_) == 0 {
                let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_6152_, 1);
                v___x_6153_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6154_ = l_Lean_Syntax_getArg(v_x_6135_, v___x_6153_);
                crate::leanh::lean_dec(v_x_6135_);
                v___x_6155_ = l_Lean_Elab_Term_Quotation_precheck(
                    v___x_6154_,
                    v_a_6136_,
                    v_a_6137_,
                    v_a_6138_,
                    v_a_6139_,
                    v_a_6140_,
                    v_a_6141_,
                    v_a_6142_,
                );
                return v___x_6155_;
            } else {
                crate::leanh::lean_dec(v_x_6135_);
                return v___x_6152_;
            }
        } else {
            crate::leanh::lean_dec(v_x_6135_);
            return v___x_6149_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinop___boxed(
    mut v_x_6156_: *mut crate::leanh::LeanObject,
    mut v_a_6157_: *mut crate::leanh::LeanObject,
    mut v_a_6158_: *mut crate::leanh::LeanObject,
    mut v_a_6159_: *mut crate::leanh::LeanObject,
    mut v_a_6160_: *mut crate::leanh::LeanObject,
    mut v_a_6161_: *mut crate::leanh::LeanObject,
    mut v_a_6162_: *mut crate::leanh::LeanObject,
    mut v_a_6163_: *mut crate::leanh::LeanObject,
    mut v_a_6164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6165_ = l_Lean_Elab_Term_Quotation_precheckBinop(
        v_x_6156_, v_a_6157_, v_a_6158_, v_a_6159_, v_a_6160_, v_a_6161_, v_a_6162_, v_a_6163_,
    );
    crate::leanh::lean_dec(v_a_6163_);
    crate::leanh::lean_dec_ref(v_a_6162_);
    crate::leanh::lean_dec(v_a_6161_);
    crate::leanh::lean_dec_ref(v_a_6160_);
    crate::leanh::lean_dec(v_a_6159_);
    crate::leanh::lean_dec_ref(v_a_6158_);
    crate::leanh::lean_dec(v_a_6157_);
    return v_res_6165_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6174_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6175_ = l_Lean_Elab_Term_Quotation_precheckBinop___closed__1;
    v___x_6176_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___closed__1;
    v___x_6177_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckBinop___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6178_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6174_,
        v___x_6175_,
        v___x_6176_,
        v___x_6177_,
    );
    return v___x_6178_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1___boxed(
    mut v_a_6179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6180_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
    return v_res_6180_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinopLazy(
    mut v_x_6187_: *mut crate::leanh::LeanObject,
    mut v_a_6188_: *mut crate::leanh::LeanObject,
    mut v_a_6189_: *mut crate::leanh::LeanObject,
    mut v_a_6190_: *mut crate::leanh::LeanObject,
    mut v_a_6191_: *mut crate::leanh::LeanObject,
    mut v_a_6192_: *mut crate::leanh::LeanObject,
    mut v_a_6193_: *mut crate::leanh::LeanObject,
    mut v_a_6194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: u8 = 0;
    v___x_6196_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1;
    crate::leanh::lean_inc(v_x_6187_);
    v___x_6197_ = l_Lean_Syntax_isOfKind(v_x_6187_, v___x_6196_);
    if v___x_6197_ == 0 {
        let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6187_);
        v___x_6198_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6198_;
    } else {
        let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6199_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6200_ = l_Lean_Syntax_getArg(v_x_6187_, v___x_6199_);
        v___x_6201_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6200_,
            v_a_6188_,
            v_a_6189_,
            v_a_6190_,
            v_a_6191_,
            v_a_6192_,
            v_a_6193_,
            v_a_6194_,
        );
        if crate::leanh::lean_obj_tag(v___x_6201_) == 0 {
            let mut v___x_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6201_, 1);
            v___x_6202_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6203_ = l_Lean_Syntax_getArg(v_x_6187_, v___x_6202_);
            v___x_6204_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6203_,
                v_a_6188_,
                v_a_6189_,
                v_a_6190_,
                v_a_6191_,
                v_a_6192_,
                v_a_6193_,
                v_a_6194_,
            );
            if crate::leanh::lean_obj_tag(v___x_6204_) == 0 {
                let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_6204_, 1);
                v___x_6205_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6206_ = l_Lean_Syntax_getArg(v_x_6187_, v___x_6205_);
                crate::leanh::lean_dec(v_x_6187_);
                v___x_6207_ = l_Lean_Elab_Term_Quotation_precheck(
                    v___x_6206_,
                    v_a_6188_,
                    v_a_6189_,
                    v_a_6190_,
                    v_a_6191_,
                    v_a_6192_,
                    v_a_6193_,
                    v_a_6194_,
                );
                return v___x_6207_;
            } else {
                crate::leanh::lean_dec(v_x_6187_);
                return v___x_6204_;
            }
        } else {
            crate::leanh::lean_dec(v_x_6187_);
            return v___x_6201_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed(
    mut v_x_6208_: *mut crate::leanh::LeanObject,
    mut v_a_6209_: *mut crate::leanh::LeanObject,
    mut v_a_6210_: *mut crate::leanh::LeanObject,
    mut v_a_6211_: *mut crate::leanh::LeanObject,
    mut v_a_6212_: *mut crate::leanh::LeanObject,
    mut v_a_6213_: *mut crate::leanh::LeanObject,
    mut v_a_6214_: *mut crate::leanh::LeanObject,
    mut v_a_6215_: *mut crate::leanh::LeanObject,
    mut v_a_6216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6217_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy(
        v_x_6208_, v_a_6209_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_, v_a_6214_, v_a_6215_,
    );
    crate::leanh::lean_dec(v_a_6215_);
    crate::leanh::lean_dec_ref(v_a_6214_);
    crate::leanh::lean_dec(v_a_6213_);
    crate::leanh::lean_dec_ref(v_a_6212_);
    crate::leanh::lean_dec(v_a_6211_);
    crate::leanh::lean_dec_ref(v_a_6210_);
    crate::leanh::lean_dec(v_a_6209_);
    return v_res_6217_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6226_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6227_ = l_Lean_Elab_Term_Quotation_precheckBinopLazy___closed__1;
    v___x_6228_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___closed__1;
    v___x_6229_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckBinopLazy___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6230_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6226_,
        v___x_6227_,
        v___x_6228_,
        v___x_6229_,
    );
    return v___x_6230_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1___boxed(
    mut v_a_6231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6232_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
    return v_res_6232_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckLeftact(
    mut v_x_6239_: *mut crate::leanh::LeanObject,
    mut v_a_6240_: *mut crate::leanh::LeanObject,
    mut v_a_6241_: *mut crate::leanh::LeanObject,
    mut v_a_6242_: *mut crate::leanh::LeanObject,
    mut v_a_6243_: *mut crate::leanh::LeanObject,
    mut v_a_6244_: *mut crate::leanh::LeanObject,
    mut v_a_6245_: *mut crate::leanh::LeanObject,
    mut v_a_6246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6249_: u8 = 0;
    v___x_6248_ = l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1;
    crate::leanh::lean_inc(v_x_6239_);
    v___x_6249_ = l_Lean_Syntax_isOfKind(v_x_6239_, v___x_6248_);
    if v___x_6249_ == 0 {
        let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6239_);
        v___x_6250_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6250_;
    } else {
        let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6251_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6252_ = l_Lean_Syntax_getArg(v_x_6239_, v___x_6251_);
        v___x_6253_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6252_,
            v_a_6240_,
            v_a_6241_,
            v_a_6242_,
            v_a_6243_,
            v_a_6244_,
            v_a_6245_,
            v_a_6246_,
        );
        if crate::leanh::lean_obj_tag(v___x_6253_) == 0 {
            let mut v___x_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6253_, 1);
            v___x_6254_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6255_ = l_Lean_Syntax_getArg(v_x_6239_, v___x_6254_);
            v___x_6256_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6255_,
                v_a_6240_,
                v_a_6241_,
                v_a_6242_,
                v_a_6243_,
                v_a_6244_,
                v_a_6245_,
                v_a_6246_,
            );
            if crate::leanh::lean_obj_tag(v___x_6256_) == 0 {
                let mut v___x_6257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_6256_, 1);
                v___x_6257_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6258_ = l_Lean_Syntax_getArg(v_x_6239_, v___x_6257_);
                crate::leanh::lean_dec(v_x_6239_);
                v___x_6259_ = l_Lean_Elab_Term_Quotation_precheck(
                    v___x_6258_,
                    v_a_6240_,
                    v_a_6241_,
                    v_a_6242_,
                    v_a_6243_,
                    v_a_6244_,
                    v_a_6245_,
                    v_a_6246_,
                );
                return v___x_6259_;
            } else {
                crate::leanh::lean_dec(v_x_6239_);
                return v___x_6256_;
            }
        } else {
            crate::leanh::lean_dec(v_x_6239_);
            return v___x_6253_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckLeftact___boxed(
    mut v_x_6260_: *mut crate::leanh::LeanObject,
    mut v_a_6261_: *mut crate::leanh::LeanObject,
    mut v_a_6262_: *mut crate::leanh::LeanObject,
    mut v_a_6263_: *mut crate::leanh::LeanObject,
    mut v_a_6264_: *mut crate::leanh::LeanObject,
    mut v_a_6265_: *mut crate::leanh::LeanObject,
    mut v_a_6266_: *mut crate::leanh::LeanObject,
    mut v_a_6267_: *mut crate::leanh::LeanObject,
    mut v_a_6268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6269_ = l_Lean_Elab_Term_Quotation_precheckLeftact(
        v_x_6260_, v_a_6261_, v_a_6262_, v_a_6263_, v_a_6264_, v_a_6265_, v_a_6266_, v_a_6267_,
    );
    crate::leanh::lean_dec(v_a_6267_);
    crate::leanh::lean_dec_ref(v_a_6266_);
    crate::leanh::lean_dec(v_a_6265_);
    crate::leanh::lean_dec_ref(v_a_6264_);
    crate::leanh::lean_dec(v_a_6263_);
    crate::leanh::lean_dec_ref(v_a_6262_);
    crate::leanh::lean_dec(v_a_6261_);
    return v_res_6269_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6278_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6279_ = l_Lean_Elab_Term_Quotation_precheckLeftact___closed__1;
    v___x_6280_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___closed__1;
    v___x_6281_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckLeftact___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6282_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6278_,
        v___x_6279_,
        v___x_6280_,
        v___x_6281_,
    );
    return v___x_6282_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1___boxed(
    mut v_a_6283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6284_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
    return v_res_6284_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckRightact(
    mut v_x_6291_: *mut crate::leanh::LeanObject,
    mut v_a_6292_: *mut crate::leanh::LeanObject,
    mut v_a_6293_: *mut crate::leanh::LeanObject,
    mut v_a_6294_: *mut crate::leanh::LeanObject,
    mut v_a_6295_: *mut crate::leanh::LeanObject,
    mut v_a_6296_: *mut crate::leanh::LeanObject,
    mut v_a_6297_: *mut crate::leanh::LeanObject,
    mut v_a_6298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: u8 = 0;
    v___x_6300_ = l_Lean_Elab_Term_Quotation_precheckRightact___closed__1;
    crate::leanh::lean_inc(v_x_6291_);
    v___x_6301_ = l_Lean_Syntax_isOfKind(v_x_6291_, v___x_6300_);
    if v___x_6301_ == 0 {
        let mut v___x_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6291_);
        v___x_6302_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6302_;
    } else {
        let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6303_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6304_ = l_Lean_Syntax_getArg(v_x_6291_, v___x_6303_);
        v___x_6305_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6304_,
            v_a_6292_,
            v_a_6293_,
            v_a_6294_,
            v_a_6295_,
            v_a_6296_,
            v_a_6297_,
            v_a_6298_,
        );
        if crate::leanh::lean_obj_tag(v___x_6305_) == 0 {
            let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6305_, 1);
            v___x_6306_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6307_ = l_Lean_Syntax_getArg(v_x_6291_, v___x_6306_);
            v___x_6308_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6307_,
                v_a_6292_,
                v_a_6293_,
                v_a_6294_,
                v_a_6295_,
                v_a_6296_,
                v_a_6297_,
                v_a_6298_,
            );
            if crate::leanh::lean_obj_tag(v___x_6308_) == 0 {
                let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_6308_, 1);
                v___x_6309_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_6310_ = l_Lean_Syntax_getArg(v_x_6291_, v___x_6309_);
                crate::leanh::lean_dec(v_x_6291_);
                v___x_6311_ = l_Lean_Elab_Term_Quotation_precheck(
                    v___x_6310_,
                    v_a_6292_,
                    v_a_6293_,
                    v_a_6294_,
                    v_a_6295_,
                    v_a_6296_,
                    v_a_6297_,
                    v_a_6298_,
                );
                return v___x_6311_;
            } else {
                crate::leanh::lean_dec(v_x_6291_);
                return v___x_6308_;
            }
        } else {
            crate::leanh::lean_dec(v_x_6291_);
            return v___x_6305_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckRightact___boxed(
    mut v_x_6312_: *mut crate::leanh::LeanObject,
    mut v_a_6313_: *mut crate::leanh::LeanObject,
    mut v_a_6314_: *mut crate::leanh::LeanObject,
    mut v_a_6315_: *mut crate::leanh::LeanObject,
    mut v_a_6316_: *mut crate::leanh::LeanObject,
    mut v_a_6317_: *mut crate::leanh::LeanObject,
    mut v_a_6318_: *mut crate::leanh::LeanObject,
    mut v_a_6319_: *mut crate::leanh::LeanObject,
    mut v_a_6320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6321_ = l_Lean_Elab_Term_Quotation_precheckRightact(
        v_x_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_, v_a_6317_, v_a_6318_, v_a_6319_,
    );
    crate::leanh::lean_dec(v_a_6319_);
    crate::leanh::lean_dec_ref(v_a_6318_);
    crate::leanh::lean_dec(v_a_6317_);
    crate::leanh::lean_dec_ref(v_a_6316_);
    crate::leanh::lean_dec(v_a_6315_);
    crate::leanh::lean_dec_ref(v_a_6314_);
    crate::leanh::lean_dec(v_a_6313_);
    return v_res_6321_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6330_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6331_ = l_Lean_Elab_Term_Quotation_precheckRightact___closed__1;
    v___x_6332_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___closed__1;
    v___x_6333_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckRightact___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6334_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6330_,
        v___x_6331_,
        v___x_6332_,
        v___x_6333_,
    );
    return v___x_6334_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1___boxed(
    mut v_a_6335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6336_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
    return v_res_6336_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckUnop(
    mut v_x_6343_: *mut crate::leanh::LeanObject,
    mut v_a_6344_: *mut crate::leanh::LeanObject,
    mut v_a_6345_: *mut crate::leanh::LeanObject,
    mut v_a_6346_: *mut crate::leanh::LeanObject,
    mut v_a_6347_: *mut crate::leanh::LeanObject,
    mut v_a_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
    mut v_a_6350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: u8 = 0;
    v___x_6352_ = l_Lean_Elab_Term_Quotation_precheckUnop___closed__1;
    crate::leanh::lean_inc(v_x_6343_);
    v___x_6353_ = l_Lean_Syntax_isOfKind(v_x_6343_, v___x_6352_);
    if v___x_6353_ == 0 {
        let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_6343_);
        v___x_6354_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Term_Quotation_precheck_spec__0_spec__6___redArg();
        return v___x_6354_;
    } else {
        let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_6355_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_6356_ = l_Lean_Syntax_getArg(v_x_6343_, v___x_6355_);
        v___x_6357_ = l_Lean_Elab_Term_Quotation_precheck(
            v___x_6356_,
            v_a_6344_,
            v_a_6345_,
            v_a_6346_,
            v_a_6347_,
            v_a_6348_,
            v_a_6349_,
            v_a_6350_,
        );
        if crate::leanh::lean_obj_tag(v___x_6357_) == 0 {
            let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_6357_, 1);
            v___x_6358_ = crate::leanh::lean_unsigned_to_nat(2);
            v___x_6359_ = l_Lean_Syntax_getArg(v_x_6343_, v___x_6358_);
            crate::leanh::lean_dec(v_x_6343_);
            v___x_6360_ = l_Lean_Elab_Term_Quotation_precheck(
                v___x_6359_,
                v_a_6344_,
                v_a_6345_,
                v_a_6346_,
                v_a_6347_,
                v_a_6348_,
                v_a_6349_,
                v_a_6350_,
            );
            return v___x_6360_;
        } else {
            crate::leanh::lean_dec(v_x_6343_);
            return v___x_6357_;
        }
    }
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckUnop___boxed(
    mut v_x_6361_: *mut crate::leanh::LeanObject,
    mut v_a_6362_: *mut crate::leanh::LeanObject,
    mut v_a_6363_: *mut crate::leanh::LeanObject,
    mut v_a_6364_: *mut crate::leanh::LeanObject,
    mut v_a_6365_: *mut crate::leanh::LeanObject,
    mut v_a_6366_: *mut crate::leanh::LeanObject,
    mut v_a_6367_: *mut crate::leanh::LeanObject,
    mut v_a_6368_: *mut crate::leanh::LeanObject,
    mut v_a_6369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6370_ = l_Lean_Elab_Term_Quotation_precheckUnop(
        v_x_6361_, v_a_6362_, v_a_6363_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_, v_a_6368_,
    );
    crate::leanh::lean_dec(v_a_6368_);
    crate::leanh::lean_dec_ref(v_a_6367_);
    crate::leanh::lean_dec(v_a_6366_);
    crate::leanh::lean_dec_ref(v_a_6365_);
    crate::leanh::lean_dec(v_a_6364_);
    crate::leanh::lean_dec_ref(v_a_6363_);
    crate::leanh::lean_dec(v_a_6362_);
    return v_res_6370_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6379_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6380_ = l_Lean_Elab_Term_Quotation_precheckUnop___closed__1;
    v___x_6381_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___closed__1;
    v___x_6382_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckUnop___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6383_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6379_,
        v___x_6380_,
        v___x_6381_,
        v___x_6382_,
    );
    return v___x_6383_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1___boxed(
    mut v_a_6384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6385_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
    return v_res_6385_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6387_ = crate::leanh::lean_box(0);
    v___x_6388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6388_, 0, v___x_6387_);
    return v___x_6388_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg___boxed(
    mut v_a_6389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6390_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
    return v_res_6390_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckHygieneInfo(
    mut v_x_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
    mut v_a_6393_: *mut crate::leanh::LeanObject,
    mut v_a_6394_: *mut crate::leanh::LeanObject,
    mut v_a_6395_: *mut crate::leanh::LeanObject,
    mut v_a_6396_: *mut crate::leanh::LeanObject,
    mut v_a_6397_: *mut crate::leanh::LeanObject,
    mut v_a_6398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6400_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo___redArg();
    return v___x_6400_;
}
pub unsafe fn l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed(
    mut v_x_6401_: *mut crate::leanh::LeanObject,
    mut v_a_6402_: *mut crate::leanh::LeanObject,
    mut v_a_6403_: *mut crate::leanh::LeanObject,
    mut v_a_6404_: *mut crate::leanh::LeanObject,
    mut v_a_6405_: *mut crate::leanh::LeanObject,
    mut v_a_6406_: *mut crate::leanh::LeanObject,
    mut v_a_6407_: *mut crate::leanh::LeanObject,
    mut v_a_6408_: *mut crate::leanh::LeanObject,
    mut v_a_6409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6410_ = l_Lean_Elab_Term_Quotation_precheckHygieneInfo(
        v_x_6401_, v_a_6402_, v_a_6403_, v_a_6404_, v_a_6405_, v_a_6406_, v_a_6407_, v_a_6408_,
    );
    crate::leanh::lean_dec(v_a_6408_);
    crate::leanh::lean_dec_ref(v_a_6407_);
    crate::leanh::lean_dec(v_a_6406_);
    crate::leanh::lean_dec_ref(v_a_6405_);
    crate::leanh::lean_dec(v_a_6404_);
    crate::leanh::lean_dec_ref(v_a_6403_);
    crate::leanh::lean_dec(v_a_6402_);
    crate::leanh::lean_dec(v_x_6401_);
    return v_res_6410_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6424_ = l_Lean_Elab_Term_Quotation_precheckAttribute;
    v___x_6425_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__0;
    v___x_6426_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___closed__2;
    v___x_6427_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Term_Quotation_precheckHygieneInfo___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_6428_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_6424_,
        v___x_6425_,
        v___x_6426_,
        v___x_6427_,
    );
    return v___x_6428_;
}
pub unsafe fn l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1___boxed(
    mut v_a_6429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6430_ = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
    return v_res_6430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Quotation_Precheck(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Quotation_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_DeprecatedSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1586858797____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Term_Quotation_quotPrecheck = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_1009736623____hygCtx___hyg_4_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Term_Quotation_quotPrecheck_allowSectionVars);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_initFn_00___x40_Lean_Elab_Quotation_Precheck_4121763900____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Elab_Term_Quotation_precheckAttribute = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Elab_Term_Quotation_precheckAttribute);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_docString__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckAttribute___regBuiltin_Lean_Elab_Term_Quotation_precheckAttribute_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckIdent___regBuiltin_Lean_Elab_Term_Quotation_precheckIdent__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckApp___regBuiltin_Lean_Elab_Term_Quotation_precheckApp__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckTypeAscription___regBuiltin_Lean_Elab_Term_Quotation_precheckTypeAscription__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckExplicit___regBuiltin_Lean_Elab_Term_Quotation_precheckExplicit__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckChoice___regBuiltin_Lean_Elab_Term_Quotation_precheckChoice__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_elabPrecheckedQuot___regBuiltin_Lean_Elab_Term_Quotation_elabPrecheckedQuot_declRange__3();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrel___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrel__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinrelNoProp___regBuiltin_Lean_Elab_Term_Quotation_precheckBinrelNoProp__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinop___regBuiltin_Lean_Elab_Term_Quotation_precheckBinop__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckBinopLazy___regBuiltin_Lean_Elab_Term_Quotation_precheckBinopLazy__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckLeftact___regBuiltin_Lean_Elab_Term_Quotation_precheckLeftact__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckRightact___regBuiltin_Lean_Elab_Term_Quotation_precheckRightact__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckUnop___regBuiltin_Lean_Elab_Term_Quotation_precheckUnop__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Quotation_Precheck_0__Lean_Elab_Term_Quotation_precheckHygieneInfo___regBuiltin_Lean_Elab_Term_Quotation_precheckHygieneInfo__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Quotation_Precheck(
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
pub unsafe fn initialize_Lean_Elab_Quotation_Precheck(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Quotation_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_DeprecatedSyntax(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Quotation_Precheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Quotation_Precheck(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Quotation_Precheck(builtin);
}
